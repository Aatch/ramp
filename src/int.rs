// Copyright 2015 The Ramp Developers
//
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
//
//        http://www.apache.org/licenses/LICENSE-2.0
//
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.

use std;
use std::cmp::{
    Ordering,
    Ord, Eq,
    PartialOrd, PartialEq
};
use std::error::Error;
use std::{fmt, hash};
use std::io;
use std::num::Zero;
use std::ops::{
    Add, Sub, Mul, Div, Rem, Neg,
    Shl, Shr, BitAnd, BitOr
};
use std::ptr::Unique;
use std::str::FromStr;
use rand::Rng;

use ll;
use ll::limb::{BaseInt, Limb};
use mem;

/**
 * An arbitrary-precision signed integer.
 *
 * This type grows to the size it needs to in order to store the result of any operation.
 *
 * ## Creation
 *
 * An `Int` can be constructed in a number of ways:
 *
 * - `Int::zero` and `Int::one` construct a zero- and one-valued `Int` respectively.
 *
 * - `Int::from` will convert from any primitive integer type to an `Int` of the same value
 *
 *   ```
 *   # use ramp::Int;
 *   let four = Int::from(4);
 *   ```
 *
 * - `Int::from_str` (or `str::parse`) will attempt to convert from a string to an `Int`
 *
 *   ```
 *   # use ramp::Int;
 *   # use std::str::FromStr;
 *   let i = Int::from_str("123456789").unwrap();
 *   ```
 *
 * ## Output
 *
 * `Int` supports all the formatting traits, allowing it to be used just like a regular integer
 * when used in `format!` and similar macros. `Int` also supports conversion to primitive integer
 * types, truncating if the `Int` cannot fit into the target type. Conversion to primtive integers
 * is done with the `From` trait:
 *
 *   ```
 *   # use ramp::Int;
 *   let big_i   = Int::from(123456789);
 *   let i = i32::from(&big_i);
 *   assert_eq!(123456789, i);
 *   ```
 *
 * ## Usage
 *
 * `Int` has a number of operator overloads to make working with them as painless as possible.
 *
 * The most basic usage is simply `a + b` or similar. Assuming `a` and `b` are of type `Int`, this
 * operation will consume both operands, reusing the storage from one of them. If you do not wish
 * your operands to be moved, one or both of them can be references: `&a + &b` works as well, but
 * requires an entire new `Int` to be allocated for the return value.
 *
 * There are also a overloads for a small number of primitive integer types, namely `i32` and
 * `usize`. While automatic type widening isn't done in Rust in general, many operations are much
 * more efficient when working with a single integer. This means you can do `a + 1` knowing that it
 * will be performed as efficiently as possible. Comparison with these integer types is also
 * possible, allowing checks for small constant values to be done easily:
 *
 *   ```
 *   # use ramp::Int;
 *   let big_i   = Int::from(123456789);
 *   assert!(big_i == 123456789);
 *   ```
 *
 * ### Semantics
 *
 * Addition, subtraction and multiplication follow the expected rules for integers. Division of two
 * integers, `N / D` is defined as producing two values: a quotient, `Q`, and a remainder, `R`,
 * such that the following equation holds: `N = Q*D + R`. The division operator itself returns `Q`
 * while the remainder/modulo operator returns `R`.
 *
 * The "bit-shift" operations are defined as being multiplication and division by a power-of-two for
 * shift-left and shift-right respectively. The sign of the number is unaffected.
 *
 * The remaining bitwise operands act as if the numbers are stored in two's complement format and as
 * if the two inputs have the same number of bits.
 *
 */
pub struct Int {
    ptr: Unique<Limb>,
    size: i32,
    cap: u32
}

impl Int {
    pub fn zero() -> Int {
        <Int as Zero>::zero()
    }

    pub fn one() -> Int {
        <Int as std::num::One>::one()
    }

    /// Creates a new Int from the given Limb.
    pub fn from_single_limb(limb: Limb) -> Int {
        let mut i = Int::with_capacity(1);
        unsafe {
            *i.ptr.get_mut() = limb;
        }
        i.size = 1;

        i
    }

    fn with_capacity(cap: u32) -> Int {
        if cap == 0 {
            return Int::zero();
        }
        unsafe {
            let ptr = mem::allocate(cap as usize);
            Int {
                ptr: Unique::new(ptr),
                size: 0,
                cap: cap
            }
        }
    }

    /**
     * Returns the sign of the Int as either -1, 0 or 1 for self being negative, zero
     * or positive, respectively.
     */
    #[inline(always)]
    pub fn sign(&self) -> i32 {
        if self.size == 0 {
            0
        } else if self.size < 0 {
            -1
        } else {
            1
        }
    }

    /**
     * Consumes self and returns the absolute value
     */
    #[inline]
    pub fn abs(mut self) -> Int {
        self.size = self.size.abs();
        self
    }

    /**
     * Returns the least-significant limb of self.
     */
    #[inline]
    pub fn to_single_limb(&self) -> Limb {
        if self.sign() == 0 {
            return Limb(0);
        } else {
            return unsafe { *self.ptr.get() };
        }
    }

    #[inline(always)]
    fn abs_size(&self) -> i32 {
        self.size.abs()
    }

    /**
     * Compare the absolute value of self to the absolute value of other,
     * returning an Ordering with the result.
     */
    pub fn abs_cmp(&self, other: &Int) -> Ordering {
        if self.abs_size() > other.abs_size() {
            Ordering::Greater
        } else if self.abs_size() < other.abs_size() {
            Ordering::Less
        } else {
            unsafe {
                ll::cmp(self.ptr.get(), other.ptr.get(), self.abs_size())
            }
        }
    }

    /**
     * Try to shrink the allocated data for this Int.
     */
    pub fn shrink_to_fit(&mut self) {
        let mut size = self.abs_size() as usize;

        if (self.cap as usize) == size { return; } // already as small as possible

        if size == 0 { size = 1; } // Keep space for at least one limb around

        unsafe {
            let old_ptr = self.ptr.get_mut() as *mut Limb as *mut u8;
            let old_cap = (self.cap as usize) * std::mem::size_of::<Limb>();
            let new_cap = size * std::mem::size_of::<Limb>();

            let new_ptr = mem::reallocate(old_ptr, old_cap, new_cap);
            self.ptr = Unique::new(new_ptr as *mut Limb);
        }
    }

    /**
     * Returns a string containing the value of self in base `base`. For bases greater than
     * ten, if `upper` is true, upper-case letters are used, otherwise lower-case ones are used.
     *
     * Panics if `base` is less than two or greater than 36.
     */
    pub fn to_str_radix(&self, base: u8, upper: bool) -> String {
        if self.size == 0 {
            return "0".to_string();
        }

        if base < 2 || base > 36 {
            panic!("Invalid base: {}", base);
        }

        let size = self.abs_size();
        let num_digits = unsafe {
            ll::base::num_base_digits(self.ptr.get(), size - 1, base as u32)
        };

        let mut buf : Vec<u8> = Vec::with_capacity(num_digits);

        self.write_radix(&mut buf, base, upper).unwrap();

        unsafe { String::from_utf8_unchecked(buf) }
    }

    pub fn write_radix<W: io::Write>(&self, w: &mut W, base: u8, upper: bool) -> io::Result<()> {
        debug_assert!(self.well_formed());

        if self.sign() == -1 {
            try!(w.write_all(b"-"));
        }

        let letter = if upper { b'A' } else { b'a' };
        let size = self.abs_size();

        unsafe {
            ll::base::to_base(base as u32, self.ptr.get(), size, |b| {
                if b < 10 {
                    w.write_all(&[b + b'0']).unwrap();
                } else {
                    w.write_all(&[(b - 10) + letter]).unwrap();
                }
            });
        }

        Ok(())
    }

    /**
     * Creates a new Int from the given string in base `base`.
     */
    pub fn from_str_radix(mut src: &str, base: u8) -> Result<Int, ParseIntError> {
        if base < 2 || base > 36 {
            panic!("Invalid base: {}", base);
        }

        if src.len() == 0 {
            return Err(ParseIntError { kind: ErrorKind::Empty });
        }

        let mut sign = 1;
        if src.starts_with('-') {
            sign = -1;
            src = &src[1..];
        }

        if src.len() == 0 {
            return Err(ParseIntError { kind: ErrorKind::Empty });
        }

        let mut buf = Vec::with_capacity(src.len());

        for c in src.bytes() {
            let b = match c {
                b'0'...b'9' => c - b'0',
                b'A'...b'Z' => (c - b'A') + 10,
                b'a'...b'z' => (c - b'a') + 10,
                _ => {
                    return Err(ParseIntError { kind: ErrorKind::InvalidDigit });
                }
            };

            if b >= base { return Err(ParseIntError { kind: ErrorKind::InvalidDigit }); }

            buf.push(b);
        }

        let num_digits = ll::base::base_digits_to_len(src.len(), base as u32);

        let mut i = Int::with_capacity(num_digits as u32);

        unsafe {
            let size = ll::base::from_base(i.ptr.get_mut(), buf.as_ptr(), buf.len() as i32, base as u32);
            i.size = (size as i32) * sign;
        }

        Ok(i)
    }

    /**
     * Divide self by other, returning the quotient, Q, and remainder, R as (Q, R).
     *
     * With N = self, D = other, Q and R satisfy: `N = QD + R`.
     */
    pub fn divmod(&self, other: &Int) -> (Int, Int) {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());
        let out_size = if self.abs_size() < other.abs_size() {
            1
        } else {
            (self.abs_size() - other.abs_size()) + 1
        };

        let out_sign = self.sign() * other.sign();
        let mut q = Int::with_capacity(out_size as u32);
        q.size = out_size * out_sign;

        let mut r = Int::with_capacity(other.abs_size() as u32);
        r.size = other.abs_size() * self.sign();

        unsafe {
            ll::divrem(q.ptr.get_mut(), r.ptr.get_mut(),
                       self.ptr.get(), self.abs_size(),
                       other.ptr.get(), other.abs_size());
        }

        q.normalize();
        r.normalize();

        (q, r)
    }

    /**
     * Raises self to the power of exp
     */
    pub fn pow(&self, mut exp: usize) -> Int {
        debug_assert!(self.well_formed());
        const CUTOFF : usize = 2 << 8;
        match exp {
            0 => Int::one(),
            1 => self.clone(),
            2 => self.square(),
            _ => {
                let mut signum = self.sign();
                if signum == 0 {
                    return Int::zero();
                }
                if exp & 1 == 0 {
                    signum = 1
                }
                let mut base = self.clone().abs();
                let mut ret = Int::one();

                let mut shift = 0;
                while base.to_single_limb() == 0 {
                    base = base >> Limb::BITS;
                    shift += Limb::BITS
                }

                let trailer : usize = base.to_single_limb().trailing_zeros() as usize;
                shift += trailer;
                base = base >> trailer;

                shift *= exp;

                if exp < CUTOFF {
                    // Simple binary
                    while exp > 0 {
                        if (exp & 1) == 1 {
                            ret = ret * &base;
                        }

                        base = base.dsquare();

                        exp /= 2;
                    }
                } else {
                    // m-ary method from Gordon, D. M. (1998). "A
                    // Survey of Fast Exponentiation Methods". Journal
                    // of Algorithms 27: 129–146.

                    let mut acc = Int::one();
                    // Is there a less awful way to do this?
                    let precomp = [{ acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() },
                                   { acc = acc * &base; acc.clone() }];

                    while exp > 0 {
                        let idx = exp & 15;
                        if idx != 0 {
                            ret = ret * &precomp[idx - 1];
                        }

                        base = base.dsquare().dsquare().dsquare().dsquare();
                        exp = exp >> 4
                    }
                }
                (ret << shift) * signum
            }
        }
    }

    /**
     * Returns the square of `self`.
     */
    pub fn square(&self) -> Int {
        debug_assert!(self.well_formed());
        let s = self.sign();
        if s == 0 {
            Int::zero()
        } else if self.abs_size() == 1 {
            let a = self.clone() * self.to_single_limb();
            if s == -1 {
                a.abs()
            } else if s == 1 {
                a
            } else {
                unreachable!()
            }
        } else {
            // There are slight faster ways of squaring very large numbers, but
            // but this is good enough for now.
            self * self
        }
    }

    // DESTRUCTIVE square. Is there a more idiomatic way of doing this?
    pub fn dsquare(mut self) -> Int {
        debug_assert!(self.well_formed());
        let s = self.sign();
        if s == 0 {
            Int::zero()
        } else if self.abs_size() == 1 {
            let l = self.to_single_limb();
            self = self * l;
            if s == -1 {
                self.abs()
            } else if s == 1 {
                self
            } else {
                unreachable!()
            }
        } else {
            // There are slight faster ways of squaring very large numbers, but
            // but this is good enough for now.
            &self * &self
        }
    }

    fn ensure_capacity(&mut self, cap: u32) {
        if cap > self.cap {
            unsafe {

                let new_ptr = if self.cap > 0 {
                    let old_ptr = self.ptr.get_mut() as *mut Limb as *mut u8;
                    let old_cap = (self.cap as usize) * std::mem::size_of::<Limb>();
                    let new_cap = (cap as usize) * std::mem::size_of::<Limb>();
                    mem::reallocate(old_ptr, old_cap, new_cap) as *mut Limb
                } else {
                    mem::allocate(cap as usize)
                };

                let mut i = self.cap;
                while i < cap {
                    *new_ptr.offset(i as isize) = Limb(0);
                    i += 1;
                }

                self.ptr = Unique::new(new_ptr);
                self.cap = cap;
            }
        }
    }

    fn push(&mut self, limb: Limb) {
        let new_size = (self.abs_size() + 1) as u32;
        self.ensure_capacity(new_size);
        unsafe {
            let pos = self.abs_size() as isize;
            *self.ptr.offset(pos) = limb;
            // If it was previously empty, then just make it positive,
            // otherwise maintain the signedness
            if self.size == 0 {
                self.size = 1;
            } else {
                self.size += self.sign();
            }
        }
    }

    /**
     * Adjust the size field so the most significant limb is non-zero
     */
    fn normalize(&mut self) {
        if self.size == 0 { true; }
        let sign = self.sign();
        unsafe {
            while self.size != 0 &&
                *self.ptr.offset((self.abs_size() - 1) as isize) == 0 {

                self.size -= sign;
            }
        }
        debug_assert!(self.well_formed());
    }

    /**
     * Make sure the Int is "well-formed", i.e. that the size doesn't exceed the
     * the capacity and that the most significant limb is non-zero
     */
    fn well_formed(&self) -> bool {
        if self.size == 0 { return true; }

        if (self.abs_size() as u32) > self.cap {
            return false;
        }

        let high_limb = unsafe {
            *self.ptr.offset((self.abs_size() - 1) as isize)
        };

        return high_limb != 0;
    }
}

impl Clone for Int {
    fn clone(&self) -> Int {
        debug_assert!(self.well_formed());

        if self.sign() == 0 {
            return Int::zero();
        }

        let mut new = Int::with_capacity(self.abs_size() as u32);
        unsafe {
            ll::copy_incr(self.ptr.get(), new.ptr.get_mut(), self.abs_size());
        }
        new.size = self.size;
        new
    }

    fn clone_from(&mut self, other: &Int) {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());

        if other.sign() == 0 {
            self.size = 0;
            return;
        }
        self.ensure_capacity(other.abs_size() as u32);
        unsafe {
            ll::copy_incr(other.ptr.get(), self.ptr.get_mut(), other.abs_size());
            self.size = other.size;
        }
    }
}

impl Drop for Int {
    fn drop(&mut self) {
        if self.cap > 0 {
            unsafe {
                let ptr = self.ptr.get_mut() as *mut Limb as *mut u8;
                let size = (self.cap as usize) * std::mem::size_of::<Limb>();
                mem::deallocate(ptr, size);
            }
            self.cap = 0;
            self.size = 0;
        }
    }
}

impl PartialEq<Int> for Int {
    #[inline]
    fn eq(&self, other: &Int) -> bool {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());
        if self.size == other.size {
            unsafe {
                ll::cmp(self.ptr.get(), other.ptr.get(), self.abs_size()) == Ordering::Equal
            }
        } else {
            false
        }
    }
}

impl PartialEq<Limb> for Int {
    #[inline]
    fn eq(&self, other: &Limb) -> bool {
        if *other == 0 && self.size == 0 {
            return true;
        }

        self.size == 1 && unsafe { *self.ptr.get() == *other }
    }
}

impl PartialEq<Int> for Limb {
    #[inline]
    fn eq(&self, other: &Int) -> bool {
        other.eq(self)
    }
}

impl Eq for Int { }

impl Ord for Int {
    #[inline]
    fn cmp(&self, other: &Int) -> Ordering {
        if self.size < other.size {
            Ordering::Less
        } else if self.size > other.size {
            Ordering::Greater
        } else { // Same number of digits and same sign
            // Check for zero
            if self.size == 0 {
                return Ordering::Equal;
            }
            unsafe {
                // If both are positive, do `self cmp other`, if both are
                // negative, do `other cmp self`
                if self.sign() == 1 {
                    ll::cmp(self.ptr.get(), other.ptr.get(), self.abs_size())
                } else {
                    ll::cmp(other.ptr.get(), self.ptr.get(), self.abs_size())
                }
            }
        }
    }
}

impl PartialOrd<Int> for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<Limb> for Int {
    #[inline]
    fn partial_cmp(&self, other: &Limb) -> Option<Ordering> {
        if self.eq(other) {
            return Some(Ordering::Equal);
        }

        if self.size < 1 {
            Some(Ordering::Less)
        } else if self.size > 1 {
            Some(Ordering::Greater)
        } else {
            unsafe {
                self.ptr.get().partial_cmp(other)
            }
        }
    }
}

impl PartialOrd<Int> for Limb {
    #[inline]
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        other.partial_cmp(self).map(|o| o.reverse())
    }
}

impl hash::Hash for Int {
    fn hash<H>(&self, state: &mut H) where H: hash::Hasher {
        debug_assert!(self.well_formed());
        self.sign().hash(state);
        let mut size = self.abs_size();
        unsafe {
            let mut ptr = self.ptr.get() as *const Limb;
            while size > 0 {
                let l = *ptr;
                l.hash(state);

                ptr = ptr.offset(1);
                size -= 1;
            }
        }
    }
}

impl Add<Limb> for Int {
    type Output = Int;

    fn add(mut self, other: Limb) -> Int {
        debug_assert!(self.well_formed());
        if other == 0 { return self; }

        // No capacity means `self` is zero. Make a new `Int` and store
        // `other` in it
        if self.cap == 0 {
            return Int::from_single_limb(other);
        }
        // This is zero, but has allocated space, so just store `other`
        if self.size == 0 {
            unsafe {
                *self.ptr.get_mut() = other;
                self.size = 1;
            }
            return self;
        }
        // `self` is non-zero, reuse the storage for the result.
        unsafe {
            let sign = self.sign();
            let size = self.abs_size();
            let ptr = self.ptr.get_mut() as *mut Limb;

            // Self is positive, just add `other`
            if sign == 1 {
                let carry = ll::add_1(ptr, ptr, size, other);
                if carry != 0 {
                    self.push(carry);
                }
            } else {
                // Self is negative, "subtract" other from self, basically doing:
                // -(-self - other) == self + other
                let borrow = ll::sub_1(ptr, ptr, size, other);
                if borrow != 0 {
                    // There was a borrow, ignore it but flip the sign on self
                    self.size = self.abs_size();
                }
            }
        }

        self
    }
}

impl<'a> Add<&'a Int> for Int {
    type Output = Int;

    fn add(mut self, other: &'a Int) -> Int {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());

        if self.sign() == 0 {
            // Try to reuse the allocation from `self`
            self.clone_from(other);
            return self;
        }
        if other.sign() == 0 {
            return self;
        }


        if self.sign() == other.sign() {
            // Signs are the same, add the two numbers together and re-apply
            // the sign after.
            let sign = self.sign();

            unsafe {
                // There's a restriction that x-size >= y-size, we can swap the operands
                // no problem, but we'd like to re-use `self`s memory if possible, so
                // if `self` is the smaller of the two we make sure it has enough space
                // for the result
                let (xp, xs, yp, ys): (*const Limb, _, *const Limb, _) = if self.abs_size() >= other.abs_size() {
                    (self.ptr.get(), self.abs_size(), other.ptr.get(), other.abs_size())
                } else {
                    self.ensure_capacity(other.abs_size() as u32);
                    (other.ptr.get(), other.abs_size(), self.ptr.get(), self.abs_size())
                };

                // Fetch the pointer first to make completely sure the compiler
                // won't make bogus claims about nonaliasing due to the &mut
                let ptr = self.ptr.get_mut() as *mut Limb;

                let carry = ll::add(ptr,
                                    xp, xs,
                                    yp, ys);
                self.size = xs * sign;
                self.normalize();

                if carry != 0 {
                    self.push(carry);
                }

                return self;
            }
        } else {
            // Signs are different, use the sign from the bigger (absolute value)
            // of the two numbers and subtract the smaller one.

            unsafe {
                let (xp, xs, yp, ys): (*const Limb, _, *const Limb, _) = if self.abs_size() > other.abs_size() {
                    (self.ptr.get(), self.size, other.ptr.get(), other.size)
                } else if self.abs_size() < other.abs_size() {
                    self.ensure_capacity(other.abs_size() as u32);
                    (other.ptr.get(), other.size, self.ptr.get(), self.size)
                } else {
                    match self.abs_cmp(other) {
                        Ordering::Equal => {
                            // They're equal, but opposite signs, so the result
                            // will be zero, clear `self` and return it
                            self.size = 0;
                            return self;
                        }
                        Ordering::Greater =>
                            (self.ptr.get(), self.size, other.ptr.get(), other.size),
                        Ordering::Less =>
                            (other.ptr.get(), other.size, self.ptr.get(), self.size)
                    }
                };

                // Fetch the pointer first to make completely sure the compiler
                // won't make bogus claims about nonaliasing due to the &mut
                let ptr = self.ptr.get_mut() as *mut Limb;

                let _borrow = ll::sub(ptr,
                                      xp, xs.abs(),
                                      yp, ys.abs());
                // There shouldn't be any borrow
                debug_assert!(_borrow == 0);

                self.size = xs;
                self.normalize();
                debug_assert!(self.abs_size() > 0);

                return self;
            }
        }
    }
}

impl<'a> Add<Int> for &'a Int {
    type Output = Int;

    fn add(self, other: Int) -> Int {
        // Forward to other + self
        other.add(self)
    }
}

impl Add<Int> for Int {
    type Output = Int;

    fn add(self, other: Int) -> Int {
        // Check for self or other being zero.
        if self.sign() == 0 {
            return other;
        }
        if other.sign() == 0 {
            return self;
        }

        let (x, y) = if self.abs_size() >= other.abs_size() {
            (self, &other)
        } else {
            (other, &self)
        };

        return x.add(y);
    }
}

impl<'a, 'b> Add<&'a Int> for &'b Int {
    type Output = Int;

    fn add(self, other: &'a Int) -> Int {
        if self.sign() == 0 {
            return other.clone();
        }
        if other.sign() == 0 {
            return self.clone();
        }

        // Clone the bigger of the two
        if self.abs_size() >= other.abs_size() {
            self.clone().add(other)
        } else {
            other.clone().add(self)
        }
    }
}

impl Sub<Limb> for Int {
    type Output = Int;

    fn sub(mut self, other: Limb) -> Int {
        debug_assert!(self.well_formed());
        if other == 0 { return self; }

        // No capacity means `self` is zero. Make a new `Int` and store
        // `other` in it
        if self.cap == 0 {
            let mut new = Int::from_single_limb(other);
            new.size = -1;
            return new;
        }
        // This is zero, but has allocated space, so just store `other`
        if self.size == 0 {
            unsafe {
                *self.ptr.get_mut() = other;
                self.size = -1;
            }
            return self;
        }
        // `self` is non-zero, reuse the storage for the result.
        unsafe {
            let sign = self.sign();
            let size = self.abs_size();
            let ptr = self.ptr.get_mut() as *mut Limb;

            // Self is negative, just "add" `other`
            if sign == -1 {
                let carry = ll::add_1(ptr, ptr, size, other);
                if carry != 0 {
                    self.push(carry);
                }
            } else {
                // Self is positive, subtract other from self
                let carry = ll::sub_1(ptr, ptr, size, other);
                self.normalize();
                if carry != 0 {
                    // There was a carry, ignore it but flip the sign on self
                    self.size = -self.abs_size();
                }
            }
        }

        debug_assert!(self.well_formed());
        self
    }
}

impl<'a> Sub<&'a Int> for Int {
    type Output = Int;

    fn sub(mut self, other: &'a Int) -> Int {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());

        // LHS is zero, return the negation of the RHS
        if self.sign() == 0 {
            self.clone_from(other);
            return -self;
        }
        // RHS is zero, return the LHS
        if other.sign() == 0 {
            return self;
        }

        if self.sign() == other.sign() {
            unsafe {
                // Signs are the same, subtract the smaller one from
                // the bigger one and adjust the sign as appropriate
                let (xp, xs, yp, ys, flip): (*const Limb, _, *const Limb, _, _) = match self.abs_cmp(other) {
                    Ordering::Equal => {
                        // x - x, just return zero
                        self.size = 0;
                        return self;
                    }
                    Ordering::Less => {
                        self.ensure_capacity(other.abs_size() as u32);
                        (other.ptr.get(), other.size, self.ptr.get(), self.size, true)
                    }
                    Ordering::Greater =>
                        (self.ptr.get(), self.size, other.ptr.get(), other.size, false)
                };

                // Fetch the pointer first to make completely sure the compiler
                // won't make bogus claims about nonaliasing due to the &mut
                let ptr = self.ptr.get_mut() as *mut Limb;

                let _borrow = ll::sub(ptr, xp, xs.abs(), yp, ys.abs());
                debug_assert!(_borrow == 0);
                self.size = if flip {
                    xs * -1
                } else {
                    xs
                };
            }

            self.normalize();
            return self;
        } else { // Different signs
            if self.sign() == -1 {
                // self is negative, use addition and negation
                let res = (-self) + other;
                return -res;
            } else {
                unsafe {
                    // Other is negative, handle as addition
                    let (xp, xs, yp, ys): (*const Limb, _, *const Limb, _) = if self.abs_size() >= other.abs_size() {
                        (self.ptr.get(), self.abs_size(), other.ptr.get(), other.abs_size())
                    } else {
                        self.ensure_capacity(other.abs_size() as u32);
                        (other.ptr.get(), other.abs_size(), self.ptr.get(), self.abs_size())
                    };

                    // Fetch the pointer first to make completely sure the compiler
                    // won't make bogus claims about nonaliasing due to the &mut
                    let ptr = self.ptr.get_mut() as *mut Limb;

                    let carry = ll::add(ptr, xp, xs, yp, ys);
                    self.size = xs;
                    self.normalize();
                    if carry != 0 {
                        self.push(carry);
                    }
                    return self;
                }
            }
        }
    }
}

impl<'a> Sub<Int> for &'a Int {
    type Output = Int;

    fn sub(self, mut other: Int) -> Int {
        if self.sign() == 0 {
            return -other;
        }
        if other.sign() == 0 {
            other.clone_from(self);
            return other;
        }

        -(other.sub(self))
    }
}

impl Sub<Int> for Int {
    type Output = Int;

    fn sub(self, other: Int) -> Int {
        if self.sign() == 0 {
            return -other;
        }
        if other.sign() == 0 {
            return self;
        }

        self.sub(&other)
    }
}

impl<'a, 'b> Sub<&'a Int> for &'b Int {
    type Output = Int;

    fn sub(self, other: &'a Int) -> Int {
        if self.sign() == 0 {
            return -other;
        }
        if other.sign() == 0 {
            return self.clone();
        }

        self.clone().sub(other)
    }
}

impl Mul<Limb> for Int {
    type Output = Int;

    fn mul(mut self, other: Limb) -> Int {
        debug_assert!(self.well_formed());
        if other == 0 || self.sign() == 0 {
            self.size = 0;
            return self;
        }

        if other == 1 {
            return self;
        }

        unsafe {
            // Fetch the pointer first to make completely sure the compiler
            // won't make bogus claims about nonaliasing due to the &mut
            let ptr = self.ptr.get_mut() as *mut Limb;

            let carry = ll::mul_1(ptr, ptr, self.abs_size(), other);
            if carry != 0 {
                self.push(carry);
            }
        }

        return self;
    }
}

impl<'a, 'b> Mul<&'a Int> for &'b Int {
    type Output = Int;

    fn mul(self, other: &'a Int) -> Int {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());
        // This is the main function, since in the general case
        // we need to allocate space for the return. Special cases
        // where this isn't necessary are handled in the other impls

        // 0 * x = 0
        if self.sign() == 0 || other.sign() == 0 {
            return Int::zero();
        }

        let out_sign = self.sign() * other.sign();

        if self.abs_size() == 1 {
            unsafe {
                let mut ret = other.clone() * *self.ptr.get();
                let size = ret.abs_size();
                ret.size = size * out_sign;
                return ret;
            }
        }
        if other.abs_size() == 1 {
            unsafe {
                let mut ret = self.clone() * *other.ptr.get();
                let size = ret.abs_size();
                ret.size = size * out_sign;
                return ret;
            }
        }

        let out_size = self.abs_size() + other.abs_size();

        let mut out = Int::with_capacity(out_size as u32);
        out.size = out_size * out_sign;

        unsafe {
            let (xp, xs, yp, ys) = if self.abs_size() >= other.abs_size() {
                (self.ptr.get(), self.abs_size(), other.ptr.get(), other.abs_size())
            } else {
                (other.ptr.get(), other.abs_size(), self.ptr.get(), self.abs_size())
            };
            ll::mul(out.ptr.get_mut(), xp, xs, yp, ys);

            // Top limb may be zero
            out.normalize();
            return out;
        }
    }
}

impl<'a> Mul<&'a Int> for Int {
    type Output = Int;

    fn mul(mut self, other: &'a Int) -> Int {
        // `other` is zero
        if other.sign() == 0 {
            self.size = 0;
            return self;
        }

        // `other` is a single limb, reuse the allocation of self
        if other.abs_size() == 1 {
            unsafe {
                let mut out = self * *other.ptr.get();
                out.size *= other.sign();
                return out;
            }
        }

        // Forward to the by-reference impl
        (&self) * other
    }
}

impl<'a> Mul<Int> for &'a Int {
    type Output = Int;

    #[inline]
    fn mul(self, other: Int) -> Int {
        // Swap arguments
        other * self
    }
}

impl Mul<Int> for Int {
    type Output = Int;

    fn mul(mut self, other: Int) -> Int {
        if self.sign() == 0 || other.sign() == 0 {
            self.size = 0;
            return self;
        }

        // One of them is a single limb big, so we can re-use the
        // allocation of the other
        if self.abs_size() == 1 {
            let val = unsafe { *self.ptr.get() };
            let mut out = other * val;
            out.size *= self.sign();
            return out;
        }
        if other.abs_size() == 1 {
            let val = unsafe { *other.ptr.get() };
            let mut out = self * val;
            out.size *= other.sign();
            return out;
        }

        // Still need to allocate for the result, just forward to
        // the by-reference impl
        (&self) * (&other)
    }
}

impl Div<Limb> for Int {
    type Output = Int;

    fn div(mut self, other: Limb) -> Int {
        debug_assert!(self.well_formed());
        if other == 0 {
            ll::divide_by_zero();
        }
        if other == 1 || self.sign() == 0 {
            return self;
        }

        unsafe {
            // Fetch the pointer first to make completely sure the compiler
            // won't make bogus claims about nonaliasing due to the &mut
            let ptr = self.ptr.get_mut() as *mut Limb;

            // Ignore the remainder
            ll::divrem_1(ptr, 0, ptr, self.abs_size(), other);
            // Adjust the size if necessary
            self.normalize();
        }

        return self;
    }
}

impl<'a, 'b> Div<&'a Int> for &'b Int {
    type Output = Int;

    fn div(self, other: &'a Int) -> Int {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());
        if other.sign() == 0 {
            ll::divide_by_zero();
        }
        if other.abs_size() == 1 {
            let l = unsafe { *other.ptr.get() };
            let out_sign = self.sign() * other.sign();
            let mut out = self.clone() / l;
            out.size = out.abs_size() * out_sign;
            return out;
        }

        self.divmod(other).0
    }
}

impl<'a> Div<&'a Int> for Int {
    type Output = Int;

    fn div(self, other: &'a Int) -> Int {
        (&self) / other
    }
}

impl<'a> Div<Int> for &'a Int {
    type Output = Int;

    fn div(self, other: Int) -> Int {
        self / (&other)
    }
}

impl Div<Int> for Int {
    type Output = Int;

    fn div(self, other: Int) -> Int {
        (&self) / (&other)
    }
}

impl Rem<Limb> for Int {
    type Output = Int;

    fn rem(mut self, other: Limb) -> Int {
        debug_assert!(self.well_formed());
        if other == 0 {
            ll::divide_by_zero();
        }
        // x % 1 == 0, 0 % n == 0
        if other == 1 || self.sign() == 0 {
            self.size = 0;
            return self;
        }

        unsafe {
            // Fetch the pointer first to make completely sure the compiler
            // won't make bogus claims about nonaliasing due to the &mut
            let ptr = self.ptr.get_mut() as *mut Limb;

            let rem = ll::divrem_1(ptr, 0, ptr, self.abs_size(), other);
            // Reuse the space from `self`, taking the sign from the numerator
            // Since `rem` has to satisfy `N = QD + R` and D is always positive,
            // `R` will always be the same sign as the numerator.
            *self.ptr.get_mut() = rem;
            let sign = self.sign();
            self.size = sign;

            if self.cap > 8 {
                // Shrink self, since it's at least 8 times bigger than necessary
                self.shrink_to_fit();
            }
        }

        return self;
    }
}

// TODO: There's probably too much cloning happening here, need to figure out
// the best way of avoiding over-copying.

impl<'a, 'b> Rem<&'a Int> for &'b Int {
    type Output = Int;

    fn rem(self, other: &'a Int) -> Int {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());
        if other.sign() == 0 {
            ll::divide_by_zero();
        }
        if other.abs_size() == 1 {
            let l = unsafe { *other.ptr.get() };
            return self.clone() % l;
        }

        self.divmod(other).1
    }
}

impl<'a> Rem<&'a Int> for Int {
    type Output = Int;

    fn rem(self, other: &'a Int) -> Int {
        (&self) % other
    }
}

impl<'a> Rem<Int> for &'a Int {
    type Output = Int;

    fn rem(self, other: Int) -> Int {
        self % (&other)
    }
}

impl Rem<Int> for Int {
    type Output = Int;

    fn rem(self, other: Int) -> Int {
        (&self) % (&other)
    }
}


impl Neg for Int {
    type Output = Int;

    #[inline]
    fn neg(mut self) -> Int {
        debug_assert!(self.well_formed());
        self.size *= -1;
        self
    }
}

impl<'a> Neg for &'a Int {
    type Output = Int;

    #[inline]
    fn neg(self) -> Int {
        self.clone().neg()
    }
}

impl Shl<usize> for Int {
    type Output = Int;

    #[inline]
    fn shl(mut self, mut cnt: usize) -> Int {
        debug_assert!(self.well_formed());
        if self.sign() == 0 { return self; }

        if cnt >= Limb::BITS as usize {
            let extra_limbs = (cnt / Limb::BITS as usize) as u32;
            debug_assert!(extra_limbs >= 1);
            cnt = cnt % Limb::BITS as usize;

            let size = self.abs_size() as u32;
            // Extend for the extra limbs, then another one for any potential extra limbs
            self.ensure_capacity(extra_limbs + size + 1);

            unsafe {
                let ptr = self.ptr.get_mut() as *mut Limb;
                let shift = ptr.offset(extra_limbs as isize);
                ll::copy_decr(ptr, shift, self.abs_size());
                ll::zero(ptr, extra_limbs as i32);
            }

            self.size += (extra_limbs as i32) * self.sign();
        }

        debug_assert!(cnt < Limb::BITS as usize);

        if cnt == 0 { return self; }

        let size = self.abs_size();

        unsafe {
            let ptr = self.ptr.get_mut() as *mut Limb;
            let c = ll::shl(ptr, ptr, size, cnt as u32);
            if c > 0 {
                self.push(c);
            }
        }

        return self;
    }
}

impl<'a> Shl<usize> for &'a Int {
    type Output = Int;

    #[inline]
    fn shl(self, cnt: usize) -> Int {
        self.clone() << cnt
    }
}

impl Shr<usize> for Int {
    type Output = Int;

    #[inline]
    fn shr(mut self, mut cnt: usize) -> Int {
        debug_assert!(self.well_formed());
        if self.sign() == 0 { return self; }

        if cnt >= Limb::BITS as usize {
            let removed_limbs = (cnt / Limb::BITS as usize) as u32;
            let size = self.abs_size();
            if removed_limbs as i32 >= size {
                return Int::zero();
            }
            debug_assert!(removed_limbs > 0);
            cnt = cnt % Limb::BITS as usize;

            unsafe {
                let ptr = self.ptr.get_mut() as *mut Limb;
                let shift = self.ptr.offset(removed_limbs as isize);

                // Shift down a whole number of limbs
                ll::copy_incr(shift, ptr, size);
                // Zero out the high limbs
                ll::zero(ptr.offset((size - (removed_limbs as i32)) as isize),
                         removed_limbs as i32);

                self.size -= (removed_limbs as i32) * self.sign();
            }
        }

        debug_assert!(cnt < Limb::BITS as usize);
        if cnt == 0 { return self; }

        let size = self.abs_size();

        unsafe {
            let ptr = self.ptr.get_mut() as *mut Limb;
            ll::shr(ptr, ptr, size, cnt as u32);
            self.normalize();
        }

        return self;
    }
}

struct ComplementSplit {
    ptr: *const Limb,
    split_idx: i32,
    len: i32
}

impl ComplementSplit {
    fn low_len(&self) -> i32 { self.split_idx }

    fn has_high_limbs(&self) -> bool {
        self.split_idx + 1 < self.len
    }
    fn high_ptr(&self) -> *const Limb {
        debug_assert!(self.has_high_limbs());
        unsafe {
            self.ptr.offset((self.split_idx + 1) as isize)
        }
    }
    fn high_len(&self) -> i32 { self.len - (self.split_idx + 1) }

    unsafe fn split_limb(&self) -> Limb {
        *self.ptr.offset(self.split_idx as isize)
    }
}

/*
 * Helper function for the bitwise operations below.
 *
 * The bitwise operations act as if the numbers are stored as two's complement integers, rather
 * than the signed magnitude representation that is actually used. Since converting to and from a
 * two's complement representation would be horribly inefficient, we split the number into three
 * segments: A number of high limbs, a single limb, the remaining zero limbs. The first segment is
 * the limbs that would be inverted in a two's complement form, the single limb is the limb
 * containing the first `1` bit. By definition, the remaining limbs must all be zero.
 *
 * This works due to the fact that `-n == !n + 1`. Consider the following bitstring, with 4-bit
 * limbs:
 *
 *     0011 0011 1101 1000 1100 0000 0000
 *
 * The two's complement of this number (with an additional "sign" bit) is:
 *
 *   1 1100 1100 0010 0111 0100 0000 0000
 *
 * As you can see, all the trailing zeros are preserved and the remaining bits are all inverted
 * with the exception of the first `1` bit. Since we prefer to work with whole limbs and not
 * individual bits we can simply take the two's complement of the limb containing that bit
 * directly.
 */
unsafe fn complement_split(np: *const Limb, len: i32) -> ComplementSplit {
    debug_assert!(len > 0);

    let bit_idx = ll::scan_1(np, len);
    let split_idx = (bit_idx / (Limb::BITS as u32)) as i32;

    ComplementSplit {
        ptr: np,
        split_idx: split_idx,
        len: len
    }
}

impl<'a> BitAnd<&'a Int> for Int {
    type Output = Int;

    fn bitand(mut self, other: &'a Int) -> Int {
        unsafe {
            let other_sign = other.sign();
            let self_sign = self.sign();

            // x & 0 == 0
            if other_sign == 0 || self_sign == 0 {
                self.size = 0;
                return self;
            }

            // Special case -1 as the two's complement is all 1s
            if *other == -1 {
                return self;
            }

            if self == -1 {
                self.clone_from(other);
                return self;
            }

            let self_ptr = self.ptr.get_mut() as *mut Limb;
            let other_ptr = other.ptr.get() as *const Limb;

            // Nice easy case both are positive
            if other_sign > 0 && self_sign > 0 {
                let size = std::cmp::min(self.abs_size(), other.abs_size());
                ll::and_n(self_ptr, self_ptr, other_ptr, size);
                self.size = size;

                self.normalize();
                return self;
            }

            // Both are negative
            if other_sign == self_sign {
                let size = std::cmp::max(self.abs_size(), other.abs_size());
                self.ensure_capacity(size as u32);
                // Copy the high limbs from other to self, if self is smaller than other
                if size > self.abs_size() {
                    ll::copy_rest(other_ptr, self_ptr, size, self.abs_size());
                }
                self.size = -size;

                let min_size = std::cmp::min(self.abs_size(), other.abs_size());

                let self_split = complement_split(self_ptr, min_size);
                let other_split = complement_split(other_ptr, min_size);

                let mut zero_limbs = std::cmp::max(self_split.low_len(), other_split.low_len());
                if zero_limbs > 0 {
                    ll::zero(self_ptr, zero_limbs);
                }

                // If the limb we split it is different for self and other, it'd be
                // zeroed out by the above step
                if self_split.low_len() == other_split.low_len() {
                    let split_ptr = self_ptr.offset(self_split.low_len() as isize);
                    *split_ptr = -(*split_ptr) & -(*other_ptr.offset(self_split.low_len() as isize));
                    zero_limbs += 1;
                }

                if zero_limbs < min_size {
                    let high_limbs = min_size - zero_limbs;
                    // Use de Morgan's Rule: !x & !y == !(x | y)
                    let self_ptr = self_ptr.offset(zero_limbs as isize);
                    let other_ptr = other_ptr.offset(zero_limbs as isize);

                    ll::nor_n(self_ptr, self_ptr, other_ptr, high_limbs);
                }

                self.normalize();
                return self;
            }

            // If we got here one is positive, the other is negative

            let (xp, yp, n) = if other_sign < 0 {
                (self_ptr as *const Limb, other_ptr, self.abs_size())
            } else {
                if other.abs_size() > self.abs_size() {
                    self.ensure_capacity(other.abs_size() as u32);
                    // Copy the high limbs from other to self
                    ll::copy_rest(other_ptr, self_ptr, other.abs_size(), self.abs_size());
                }
                (other_ptr, self_ptr as *const Limb, other.abs_size())
            };

            // x > 0, y < 0
            let self_ptr = self.ptr.get_mut() as *mut Limb;
            let y_split = complement_split(yp, n);

            let split = y_split.split_idx as isize;
            ll::zero(self_ptr, y_split.low_len());

            *self_ptr.offset(split) = *xp.offset(split) & -y_split.split_limb();

            if y_split.has_high_limbs() {
                ll::and_not_n(self_ptr.offset(split + 1), xp.offset(split + 1), y_split.high_ptr(),
                              y_split.high_len());
            }

            self.size = n;
            self.normalize();
            return self;
        }
    }
}

impl<'a> BitAnd<Int> for &'a Int {
    type Output = Int;

    #[inline]
    fn bitand(self, other: Int) -> Int {
        other.bitand(self)
    }
}

impl<'a, 'b> BitAnd<&'a Int> for &'b Int {
    type Output = Int;

    #[inline]
    fn bitand(self, other: &'a Int) -> Int {
        self.clone().bitand(other)
    }
}

impl BitAnd<Int> for Int {
    type Output = Int;

    #[inline]
    fn bitand(self, other: Int) -> Int {
        self.bitand(&other)
    }
}

impl<'a> BitOr<&'a Int> for Int {
    type Output = Int;

    fn bitor(mut self, other: &'a Int) -> Int {
        unsafe {
            if *other == 0 {
                return self;
            }
            if self == 0 {
                self.clone_from(other);
                return self;
            }

            if *other == -1 || self == -1 {
                self.size = -1;
                *self.ptr.get_mut() = Limb(1);
                return self;
            }

            let self_sign = self.sign();
            let other_sign = other.sign();

            let self_ptr = self.ptr.get_mut() as *mut Limb;
            let other_ptr = other.ptr.get() as *const Limb;

            if self_sign > 0 && other_sign > 0 {
                let size = std::cmp::max(self.abs_size(), other.abs_size());
                self.ensure_capacity(size as u32);
                if size > self.abs_size() {
                    ll::copy_rest(other_ptr, self_ptr, size, self.abs_size());
                }

                let min_size = std::cmp::min(self.abs_size(), other.abs_size());
                ll::or_n(self_ptr, self_ptr, other_ptr, min_size);

                self.size = size;
                return self;
            }

            if self_sign == other_sign {
                let min_size = std::cmp::min(self.abs_size(), other.abs_size());

                let self_split = complement_split(self_ptr, min_size);
                let other_split = complement_split(other_ptr, min_size);

                if self_split.low_len() > other_split.low_len() {
                    let mut p = self_ptr.offset(other_split.low_len() as isize);

                    *p = -other_split.split_limb();
                    p = p.offset(1);
                    let mut o = other_ptr.offset((other_split.low_len() + 1) as isize);
                    let mut n = (self_split.low_len() - other_split.low_len()) - 1;

                    while n > 0 {
                        *p = !(*o);
                        p = p.offset(1);
                        o = o.offset(1);
                        n -= 1;
                    }
                }

                let low_limbs = std::cmp::max(self_split.low_len(), other_split.low_len()) + 1;
                if low_limbs < min_size {
                    let high_limbs = min_size - low_limbs;
                    let o = other_ptr.offset(low_limbs as isize);
                    let s = self_ptr.offset(low_limbs as isize);
                    // de Morgan's Rule: !x | !y == !(x & y)
                    ll::nand_n(s, s, o, high_limbs);
                }

                self.size = -min_size;
                self.normalize();

                return self;
            }


            // If we got here one is positive, the other is negative

            let n = std::cmp::max(other.abs_size(), self.abs_size());
            self.ensure_capacity(n as u32);
            let (xp, yp) = if other_sign < 0 {
                (self_ptr as *const Limb, other_ptr)
            } else {
                (other_ptr, self_ptr as *const Limb)
            };

            // x > 0, y < 0
            let y_split = complement_split(yp, n);
            let split = y_split.low_len() as isize;

            if xp != self_ptr {
                ll::copy_incr(xp, self_ptr, y_split.low_len());
            }

            *self_ptr.offset(split) = *xp.offset(split) | -y_split.split_limb();

            if y_split.has_high_limbs() {
                ll::or_not_n(self_ptr.offset(split + 1), xp.offset(split + 1), y_split.high_ptr(),
                             y_split.high_len());
            }

            self.size = -n;
            self.normalize();
            return self;
        }
    }
}

impl<'a> BitOr<Int> for &'a Int {
    type Output = Int;

    #[inline]
    fn bitor(self, other: Int) -> Int {
        other.bitor(self)
    }
}

impl<'a, 'b> BitOr<&'a Int> for &'b Int {
    type Output = Int;

    #[inline]
    fn bitor(self, other: &'a Int) -> Int {
        self.clone().bitor(other)
    }
}

impl BitOr<Int> for Int {
    type Output = Int;

    #[inline]
    fn bitor(self, other: Int) -> Int {
        self.bitor(&other)
    }
}

macro_rules! impl_arith_prim (
    (signed $t:ty) => (
        // Limbs are unsigned, so make sure we account for the sign
        // when $t is signed
        impl Add<$t> for Int {
            type Output = Int;

            #[inline]
            fn add(self, other: $t) -> Int {
                if other == 0 {
                    return self;
                }
                if other < 0 {
                    return self - Limb(other.abs() as BaseInt);
                }
                return self + Limb(other as BaseInt);
            }
        }

        impl Sub<$t> for Int {
            type Output = Int;

            #[inline]
            fn sub(self, other: $t) -> Int {
                if other == 0 {
                    return self;
                }
                if other < 0 {
                    return self + Limb(other.abs() as BaseInt);
                }
                return self - Limb(other as BaseInt);
            }
        }

        impl Mul<$t> for Int {
            type Output = Int;

            #[inline]
            fn mul(mut self, other: $t) -> Int {
                if other == 0 {
                    self.size = 0;
                    return self;
                }
                if other == 1 || self.sign() == 0 {
                    return self;
                }
                if other == -1 {
                    return -self;
                }
                if other < 0 {
                    return -self * Limb(other.abs() as BaseInt);
                }
                return self * Limb(other as BaseInt);
            }
        }

        impl Div<$t> for Int {
            type Output = Int;

            #[inline]
            fn div(self, other: $t) -> Int {
                if other == 0 {
                    ll::divide_by_zero();
                }
                if other == 1 || self.sign() == 0 {
                    return self;
                }
                if other == -1 {
                    return -self;
                }
                if other < 0 {
                    return -self / Limb(other.abs() as BaseInt);
                }
                return self / Limb(other as BaseInt);
            }
        }

        impl Rem<$t> for Int {
            type Output = Int;

            #[inline]
            fn rem(mut self, other: $t) -> Int {
                if other == 0 {
                    ll::divide_by_zero();
                }

                if other == 1 ||other == -1 || self.sign() == 0 {
                    self.size = 0;
                    return self;
                }

                return self / Limb(other as BaseInt);
            }
        }

        impl_arith_prim!(common $t);
    );
    (unsigned $t:ty) => (
        impl Add<$t> for Int {
            type Output = Int;

            #[inline]
            fn add(self, other: $t) -> Int {
                if other == 0 {
                    return self;
                }
                return self + Limb(other as BaseInt);
            }
        }

        impl Sub<$t> for Int {
            type Output = Int;

            #[inline]
            fn sub(self, other: $t) -> Int {
                if other == 0 {
                    return self;
                }
                return self - Limb(other as BaseInt);
            }
        }

        impl Mul<$t> for Int {
            type Output = Int;

            #[inline]
            fn mul(mut self, other: $t) -> Int {
                if other == 0 {
                    self.size = 0;
                    return self;
                }
                if other == 1 || self.sign() == 0 {
                    return self;
                }
                return self * Limb(other as BaseInt);
            }
        }

        impl Div<$t> for Int {
            type Output = Int;

            #[inline]
            fn div(self, other: $t) -> Int {
                if other == 0 {
                    ll::divide_by_zero();
                }
                if other == 1 || self.sign() == 0 {
                    return self;
                }
                return self / Limb(other as BaseInt);
            }
        }

        impl Rem<$t> for Int {
            type Output = Int;

            #[inline]
            fn rem(mut self, other: $t) -> Int {
                if other == 0 {
                    ll::divide_by_zero();
                }

                if other == 1 || self.sign() == 0 {
                    self.size = 0;
                    return self;
                }

                return self / Limb(other as BaseInt);
            }
        }
        impl_arith_prim!(common $t);
    );
    (common $t:ty) => (
        // Common impls, these should just forward to the above
        // impls
        impl<'a> Add<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn add(self, other: $t) -> Int {
                self.clone() + other
            }
        }

        impl Add<Int> for $t {
            type Output = Int;

            #[inline]
            fn add(self, other: Int) -> Int {
                return other + self;
            }
        }

        impl<'a> Add<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn add(self, other: &'a Int) -> Int {
                other.clone() + self
            }
        }

        impl<'a> Sub<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn sub(self, other: $t) -> Int {
                self.clone() - other
            }
        }

        impl Sub<Int> for $t {
            type Output = Int;

            #[inline]
            fn sub(self, other: Int) -> Int {
                -other + self
            }
        }

        impl<'a> Sub<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn sub(self, other: &'a Int) -> Int {
                -(other - self)
            }
        }

        impl<'a> Mul<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn mul(self, other: $t) -> Int {
                return self.clone() * other;
            }
        }

        impl Mul<Int> for $t {
            type Output = Int;

            #[inline]
            fn mul(self, other: Int) -> Int {
                other * self
            }
        }

        impl<'a> Mul<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn mul(self, other: &'a Int) -> Int {
                // Check for zero here to avoid cloning unnecessarily
                if self == 0 { return Int::zero() };
                other.clone() * self
            }
        }

        impl<'a> Div<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn div(self, other: $t) -> Int {
                if other == 0 {
                    ll::divide_by_zero();
                }
                return self.clone() / other;
            }
        }

        impl Div<Int> for $t {
            type Output = Int;

            #[inline]
            fn div(self, mut other: Int) -> Int {
                if self == 0 {
                    other.size = 0;
                    return other;
                }
                if other.sign() == 0 {
                    ll::divide_by_zero();
                }
                // There's probably a better way of doing this, but
                // I don't see n / <bigint> being common in code
                Int::from(self) / other
            }
        }

        impl<'a> Div<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn div(self, other: &'a Int) -> Int {
                if self == 0 { return Int::zero() };
                if other.sign() == 0 {
                    ll::divide_by_zero();
                }

                self / other.clone()
            }
        }

        impl<'a> Rem<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn rem(self, other: $t) -> Int {
                if other == 0 {
                    ll::divide_by_zero();
                }
                if self.sign() == 0 || other == 1 {
                    return Int::zero()
                };
                return self.clone() % other;
            }
        }

        impl Rem<Int> for $t {
            type Output = Int;

            #[inline]
            fn rem(self, mut other: Int) -> Int {
                if self == 0 || other == 1 {
                    other.size = 0;
                    return other;
                }
                if other.sign() == 0 {
                    ll::divide_by_zero();
                }
                // There's probably a better way of doing this, but
                // I don't see n % <bigint> being common in code
                Int::from(self) % other
            }
        }

        impl<'a> Rem<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn rem(self, other: &'a Int) -> Int {
                if self == 0 { return Int::zero() };
                if other.sign() == 0 {
                    ll::divide_by_zero();
                }

                self % other.clone()
            }
        }

    )
);

// Implement for `i32` which is the fallback type, usize and the base integer type.
// No more than this because the rest of Rust doesn't much coercion for integer types,
// but allocating an entire multiple-precision `Int` to do `+ 1` seems silly.
impl_arith_prim!(signed i32);
impl_arith_prim!(unsigned usize);
impl_arith_prim!(unsigned BaseInt);

impl PartialEq<i32> for Int {
    #[inline]
    fn eq(&self, &other: &i32) -> bool {
        let sign = self.sign();
        // equals zero
        if sign == 0 || other == 0 {
            return other == sign;
        }
        // Differing signs
        if sign < 0 && other > 0 || sign > 0 && other < 0 {
            return false;
        }

        // We can't fall back to the `== Limb` impl when self is negative
        // since it'll fail because of signs
        if sign < 0 {
            if self.abs_size() > 1 { return false; }
            unsafe {
                return *self.ptr.get() == (other.abs() as BaseInt);
            }
        }

        self.eq(&Limb(other.abs() as BaseInt))
    }
}

impl PartialEq<Int> for i32 {
    #[inline]
    fn eq(&self, other: &Int) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<i32> for Int {
    #[inline]
    fn partial_cmp(&self, &other: &i32) -> Option<Ordering> {
        let self_sign = self.sign();
        let other_sign = if other < 0 {
            -1
        } else if other > 0 {
            1
        } else {
            0
        };

        // Both are equal
        if self_sign == 0 && other_sign == 0 {
            return Some(Ordering::Equal);
        }

        let ord = if self_sign > other_sign {
            Ordering::Greater
        } else if self_sign < other_sign {
            Ordering::Less
        } else { // Now both signs are the same, and non-zero

            if self_sign < 0 {
                if self.abs_size() > 1 {
                    Ordering::Less
                } else {
                    self.to_single_limb().cmp(&Limb(other.abs() as BaseInt)).reverse()
                }
            } else {
                return self.partial_cmp(&Limb(other.abs() as BaseInt));
            }
        };

        Some(ord)
    }
}

impl PartialOrd<Int> for i32 {
    #[inline]
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        other.partial_cmp(self).map(|o| o.reverse())
    }
}

impl PartialEq<usize> for Int {
    #[inline]
    fn eq(&self, &other: &usize) -> bool {
        return self.eq(&Limb(other as BaseInt));
    }
}

impl PartialEq<Int> for usize {
    #[inline]
    fn eq(&self, other: &Int) -> bool {
        other.eq(self)
    }
}

impl PartialOrd<usize> for Int {
    #[inline]
    fn partial_cmp(&self, &other: &usize) -> Option<Ordering> {
        self.partial_cmp(&Limb(other as BaseInt))
    }
}

impl PartialOrd<Int> for usize {
    #[inline]
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Limb(*self as BaseInt).partial_cmp(other)
    }
}

macro_rules! impl_from_prim (
    (signed $($t:ty),*) => {
        $(impl ::std::convert::From<$t> for Int {
            #[allow(exceeding_bitshifts)] // False positives for the larger-than BaseInt case
            fn from(val: $t) -> Int {
                if val == 0 {
                    return Int::zero();
                }
                // Handle i64/u64 on 32-bit platforms.
                if std::mem::size_of::<$t>() > std::mem::size_of::<BaseInt>() {
                    let vabs = val.abs();
                    let mask : BaseInt = !0;
                    let vlow = vabs & (mask as $t);
                    let vhigh = vabs >> Limb::BITS;

                    let low_limb = Limb(vlow as BaseInt);
                    let high_limb = Limb(vhigh as BaseInt);
                    let mut i = Int::from_single_limb(low_limb);
                    if high_limb != 0 {
                        i.push(high_limb);
                    }

                    if val < 0 {
                        i.size *= -1;
                    }

                    return i;
                } else {
                    let limb = Limb(val.abs() as BaseInt);
                    let mut i = Int::from_single_limb(limb);
                    if val < 0 {
                        i.size *= -1;
                    }

                    return i;
                }
            }
        })*
    };
    (unsigned $($t:ty),*) => {
        $(impl ::std::convert::From<$t> for Int {
            #[allow(exceeding_bitshifts)] // False positives for the larger-than BaseInt case
            fn from(val: $t) -> Int {
                if val == 0 {
                    return Int::zero();
                }
                // Handle i64/u64 on 32-bit platforms.
                if std::mem::size_of::<$t>() > std::mem::size_of::<BaseInt>() {
                    let mask : BaseInt = !0;
                    let vlow = val & (mask as $t);
                    let vhigh = val >> Limb::BITS;

                    let low_limb = Limb(vlow as BaseInt);
                    let high_limb = Limb(vhigh as BaseInt);
                    let mut i = Int::from_single_limb(low_limb);
                    if high_limb != 0 {
                        i.push(high_limb);
                    }

                    return i;
                } else {
                    let limb = Limb(val as BaseInt);
                    return Int::from_single_limb(limb);
                }
            }
        })*
    }
);

impl_from_prim!(signed   i8, i16, i32, i64, isize);
impl_from_prim!(unsigned u8, u16, u32, u64, usize);

// Number formatting - There's not much difference between the impls,
// hence the macro

macro_rules! impl_fmt (
    ($t:path, $radix:expr, $upper:expr, $prefix:expr) => {
        impl $t for Int {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let mut s : &str = &self.to_str_radix($radix, $upper);
                let is_positive = self.sign() >= 0;
                // to_str_radix adds the sign if `self` is negative, but
                // pad_integral adds it's own sign, so slice the sign off
                if !is_positive {
                    s = &s[1..];
                }

                f.pad_integral(is_positive, $prefix, s)
            }
        }
    };

    ($t:path, $radix:expr, $prefix:expr) => {
        impl_fmt!($t, $radix, false, $prefix);
    }
);

impl_fmt!(fmt::Binary,    2, "0b");
impl_fmt!(fmt::Octal,     8, "0o");
impl_fmt!(fmt::Display,  10, "");
impl_fmt!(fmt::Debug,    10, "");
impl_fmt!(fmt::LowerHex, 16, false, "0x");
impl_fmt!(fmt::UpperHex, 16, true, "0x");

// String parsing

#[derive(Debug, Clone, PartialEq)]
pub struct ParseIntError { kind: ErrorKind }

#[derive(Debug, Clone, PartialEq)]
enum ErrorKind {
    Empty,
    InvalidDigit
}

impl Error for ParseIntError {
    fn description<'a>(&'a self) -> &'a str {
        match self.kind {
            ErrorKind::Empty => "cannot parse empty string",
            ErrorKind::InvalidDigit => "invalid digit found in string"
        }
    }
}

impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.description().fmt(f)
    }
}

impl FromStr for Int {
    type Err = ParseIntError;

    fn from_str(src: &str) -> Result<Int, ParseIntError> {
        Int::from_str_radix(src, 10)
    }
}

// Conversion *to* primitives via the From trait.

macro_rules! impl_from_for_prim (
    (signed $($t:ty),*) => (
        $(impl<'a> ::std::convert::From<&'a Int> for $t {
            #[allow(exceeding_bitshifts)] // False positives for the larger-than BaseInt case
            fn from(i: &'a Int) -> $t {
                let sign = i.sign() as $t;
                if sign == 0 {
                    return 0;
                }
                let mask = !0 >> 1;
                if ::std::mem::size_of::<BaseInt>() < ::std::mem::size_of::<$t>() {
                    // Handle conversion where BaseInt = u32 and $t = i64
                    if i.abs_size() >= 2 { // Fallthrough if there's only one limb
                        let lower = i.to_single_limb().0 as $t;
                        // Clear the highest bit of the high limb
                        let higher = (unsafe { (*i.ptr.offset(1)).0 } & mask) as $t;

                        // Combine the two
                        let n : $t = lower & (higher << Limb::BITS);

                        // Apply the sign
                        return n * sign;
                    }
                }
                let n = i.to_single_limb().0;
                return (n as $t) * sign;
            }
        })*
    );
    (unsigned $($t:ty),*) => (
        $(impl<'a> ::std::convert::From<&'a Int> for $t {
            #[allow(exceeding_bitshifts)] // False positives for the larger-than BaseInt case
            fn from(i: &'a Int) -> $t {
                // This does the conversion ignoring the sign

                if i.sign() == 0 {
                    return 0;
                }
                if ::std::mem::size_of::<BaseInt>() < ::std::mem::size_of::<$t>() {
                    // Handle conversion where BaseInt = u32 and $t = u64
                    if i.abs_size() >= 2 { // Fallthrough if there's only one limb
                        let lower = i.to_single_limb().0 as $t;
                        let higher = unsafe { (*i.ptr.offset(1)).0 } as $t;

                        // Combine the two
                        let n : $t = lower & (higher << Limb::BITS);

                        return n;
                    }
                }
                let n = i.to_single_limb().0;
                return n as $t;
            }
        })*
    )
);

impl_from_for_prim!(signed   i8, i16, i32, i64, isize);
impl_from_for_prim!(unsigned u8, u16, u32, u64, usize);

impl std::num::Zero for Int {
    fn zero() -> Int {
        Int {
            ptr: unsafe { Unique::new(std::rt::heap::EMPTY as *mut Limb) },
            size: 0,
            cap: 0
        }
    }
}

impl std::num::One for Int {
    fn one() -> Int {
        Int::from(1)
    }
}

impl std::iter::Step for Int {
    fn step(&self, by: &Int) -> Option<Int> {
        Some(self + by)
    }

    fn steps_between(start: &Int, end: &Int, by: &Int) -> Option<usize> {
        if by.le(&0) { return None; }
        let mut diff = (start - end).abs();
        if by.ne(&1) {
            diff = diff / by;
        }

        // Check to see if result fits in a usize
        if diff > !0usize {
            None
        } else {
            Some(usize::from(&diff))
        }
    }
}

pub trait RandomInt {
    /// Generate a random unsigned `Int` of given bit size.
    fn gen_uint(&mut self, bits: usize) -> Int;
    /// Generate a random `Int` of given bit size.
    fn gen_int(&mut self, bits: usize) -> Int;
    /// Generate a random unsigned `Int` less than the given bound.
    /// Fails when the bound is zero or negative.
    fn gen_uint_below(&mut self, bound: &Int) -> Int;
    /// Generate a random `Int` within the given range.
    /// The lower bound is inclusive; the upper bound is exclusive.
    /// Fails when the upper bound is not greater than the lower bound.
    fn gen_int_range(&mut self, lbound: &Int, ubound: &Int) -> Int;
}

impl<R: Rng> RandomInt for R {
    fn gen_uint(&mut self, bits: usize) -> Int {
        let digits = (bits / &ll::limb::Limb::BITS) as u32;
        let rem = bits % &ll::limb::Limb::BITS;

        let mut data = Int::with_capacity(digits + 1);

        for _ in (0 .. digits) {
            let limb = Limb(self.gen());
            data.push(limb);
        }

        if rem > 0 {
            let final_digit = Limb(self.gen());
            data.push(final_digit >> (&ll::limb::Limb::BITS - rem));
        }

        data.normalize();

        data
    }

    fn gen_int(&mut self, bits: usize) -> Int {

        let data = self.gen_uint(bits);

        let r = if data == Int::zero() {
            // ...except that if the BigUint is zero, we need to try
            // again with probability 0.5. This is because otherwise,
            // the probability of generating a zero BigInt would be
            // double that of any other number.
            if self.gen() {
             return self.gen_uint(bits);
            } else {
             data
            }
        } else if self.gen() {
            -data
        } else {
            data
        };

        r
    }

    fn gen_uint_below(&mut self, bound: &Int) -> Int {
        assert!(*bound > Int::zero());

        let mut i = (*bound).clone();
        i.normalize();

        let lz = bound.to_single_limb().leading_zeros() as i32;
        let bits = ((bound.abs_size() * Limb::BITS as i32) - lz) as usize;

        loop {
            let n = self.gen_uint(bits);
            if n < *bound { return n; }
        }
    }

    fn gen_int_range(&mut self, lbound: &Int, ubound: &Int) -> Int {
        assert!(*lbound < *ubound);
        return lbound + self.gen_uint_below(&(ubound - lbound));
    }
}

#[cfg(test)]
pub fn rand_int<R: ::rand::Rng>(rng: &mut R, limbs: u32) -> Int {
    let negative : bool = rng.gen();

    let mut i = Int::with_capacity(limbs);
    for _ in 0..limbs {
        let limb = Limb(rng.gen());
        i.push(limb);
    }

    i.normalize();

    if negative {
        -i
    } else {
        i
    }
}

#[cfg(test)]
mod test {
    use std;
    use std::hash::{Hash, Hasher};
    use rand::{self, Rng};
    use test::{self, Bencher};
    use super::*;
    use std::str::FromStr;
    use std::num::Zero;

    macro_rules! assert_mp_eq (
        ($l:expr, $r:expr) => (
            {
                let l = $l;
                let r = $r;
                if l != r {
                    println!("assertion failed: {} == {}", stringify!($l), stringify!($r));
                    panic!("{:} != {:}", l, r);
                }
            }
        )
    );

    #[test]
    fn gen_int() {
        let mut rng = rand::thread_rng();

        let big_i = rng.gen_int(7);

        println!("{}", big_i);
    }

    #[test]
    fn gen_uint() {
        let mut rng = rand::thread_rng();

        let big_i = rng.gen_uint(32);

        println!("{}", big_i);
    }

    #[test]
    fn gen_uint_below() {
        let mut rng = rand::thread_rng();

        let big_i = rng.gen_uint_below(&Int::from(20));

        println!("{}", big_i);
    }

    #[test]
    fn gen_int_range() {
        let mut rng = rand::thread_rng();

        let big_i = rng.gen_int_range(&Int::from(-20), &Int::from(20));

        println!("{}", big_i);
    }

    #[test]
    fn from_string_10() {
        let cases = [
            ("0",        0i32),
            ("123456",   123456),
            ("0123",     123),
            ("000000",   0),
            ("-0",       0),
            ("-1",       -1),
            ("-123456", -123456),
            ("-0123",   -123),
        ];

        for &(s, n) in cases.iter() {
            let i : Int = s.parse().unwrap();
            assert_eq!(i, n);
        }
    }

    #[test]
    fn from_string_16() {
        let cases = [
            ("0",        0i32),
            ("abcde",    0xabcde),
            ("0ABC",     0xabc),
            ("12AB34cd", 0x12ab34cd),
            ("-ABC",    -0xabc),
            ("-0def",   -0xdef),
        ];

        for &(s, n) in cases.iter() {
            let i : Int = Int::from_str_radix(s, 16).unwrap();
            assert!(i == n, "Assertion failed: {:#x} != {:#x}", i, n);
        }
    }

    #[test]
    fn to_string_10() {
        let cases = [
            ("0",        Int::zero()),
            ("1",        Int::from(1)),
            ("123",      Int::from(123)),
            ("-456",     Int::from(-456)),
            ("987654321012345678910111213",
             Int::from_str("987654321012345678910111213").unwrap()),
        ];

        for &(s, ref n) in cases.iter() {
            assert_eq!(s, &n.to_string());
        }
    }

    #[test]
    fn to_string_16() {
        let cases = [
            ("0",        Int::zero()),
            ("1",        Int::from(1)),
            ("-1",       Int::from(-1)),
            ("abc",      Int::from(0xabc)),
            ("-456",     Int::from(-0x456)),
            ("987654321012345678910111213",
             Int::from_str_radix("987654321012345678910111213", 16).unwrap()),
        ];

        for &(s, ref n) in cases.iter() {
            assert_eq!(s, &n.to_str_radix(16, false));
        }
    }

    #[test]
    fn pow() {
        let bases = ["0", "1", "190000000000000", "192834857324591531",
                     "100000000", "-1", "-100", "-200", "-192834857324591531",
                     "-431343873217510631841"];

        for b in bases.iter() {
            let b : Int = b.parse().unwrap();
            let mut x = Int::one();
            for e in 0..512 {
                let a = &b.pow(e);
                // println!("b={}, e={}, a={}, x={}", &b, &e, &a, &x);
                assert_mp_eq!(a.clone(), x.clone());
                x = &x * &b
            }
        }
    }

    #[test]
    fn add() {
        let cases = [
            ("0", "0", "0"),
            ("1", "0", "1"),
            ("1", "1", "2"),
            ("190000000000000", "1", "190000000000001"),
            ("192834857324591531", "431343873217510631841", "431536708074835223372"),
            ("0", "-1", "-1"),
            ("1", "-1", "0"),
            ("100000000", "-1", "99999999"),
            ("-100", "-100", "-200"),
            ("-192834857324591531", "-431343873217510631841", "-431536708074835223372"),
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            assert_mp_eq!(l + r, a);
        }
    }

    #[test]
    fn sub() {
        let cases = [
            ("0", "0", "0"),
            ("1", "0", "1"),
            ("1", "1", "0"),
            ("0", "1", "-1"),
            ("190000000000000", "1", "189999999999999"),
            ("192834857324591531", "431343873217510631841", "-431151038360186040310"),
            ("0", "-1", "1"),
            ("1", "-1", "2"),
            ("100000000", "-1", "100000001"),
            ("-100", "-100", "0"),
            ("-100", "100", "-200"),
            ("-192834857324591531", "-431343873217510631841", "431151038360186040310")
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            assert_mp_eq!(&l - &r, a.clone());
            assert_mp_eq!(&l - r.clone(), a.clone());
            assert_mp_eq!(l.clone() - &r, a.clone());
            assert_mp_eq!(l - r, a);
        }
    }

    #[test]
    fn mul() {
        let cases = [
            ("0", "0", "0"),
            ("1", "0", "0"),
            ("1", "1", "1"),
            ("1234", "-1", "-1234"),
            ("8", "9", "72"),
            ("-8", "-9", "72"),
            ("8", "-9", "-72"),
            ("1234567891011", "9876543210123", "12193263121400563935904353"),
            ("-1234567891011", "9876543210123", "-12193263121400563935904353"),
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            assert_mp_eq!(l * r, a);
        }
    }

    #[test]
    fn div() {
        let cases = [
            ("1", "1", "1"),
            ("1234", "-1", "-1234"),
            ("8", "9", "0"),
            ("-9", "-3", "3"),
            ("1234567891011121314151617", "95123654789852856006", "12978"),
            ("-1234567891011121314151617", "95123654789852856006", "-12978"),
            ("-1198775410753307067346230628764044530011323809665206377243907561641040294348297309637331525393593945901384203950086960228531308793518800829453656715578105987032036211272103322425770761458186593",
             "979504192721382235629958845425279521512826176107035761459344386626944187481828320416870752582555",
             "-1223859397092234843008309150569447886995823751180958876260102037121722431272801092547910923059616")
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = &l / &r;
            assert_mp_eq!(val, a);
        }
    }

    #[test]
    fn bitand() {
        let cases = [
            ("0", "543253451643657932075830214751263521", "0"),
            ("-1", "543253451643657932075830214751263521", "543253451643657932075830214751263521"),
            ("47398217493274092174042109472", "9843271092740214732017421", "152974816756326460458496"),
            ("87641324986400000000000", "31470973247490321000000000000000", "2398658832415825854464")
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = &l & &r;
            assert_mp_eq!(val, a);
        }
    }

    #[test]
    fn bitor() {
        let cases = [
            ("0", "543253451643657932075830214751263521", "543253451643657932075830214751263521"),
            ("-1", "543253451643657932075830214751263521", "-1"),
            ("47398217493274092174042109472", "9843271092740214732017421","47407907789550076062313668397"),
            ("87641324986400000000000", "31470973247490321000000000000000", "31470973332732987153984174145536"),
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = &l | &r;
            assert_mp_eq!(val, a);
        }
    }

    const RAND_ITER : usize = 1000;

    #[test]
    fn div_rand() {
        let mut rng = rand::thread_rng();
        for _ in (0..RAND_ITER) {
            let x = rand_int(&mut rng, 10);
            let y = rand_int(&mut rng, 5);

            let (q, r) = x.divmod(&y);
            let val = (q * &y) + r;

            assert_mp_eq!(val, x);
        }
    }

    #[test]
    fn shl_rand() {
        let mut rng = rand::thread_rng();
        for _ in (0..RAND_ITER) {
            let x = rand_int(&mut rng, 10);

            let shift_1 = &x << 1;
            let mul_2 = &x * 2;

            assert_mp_eq!(shift_1, mul_2);

            let shift_3 = &x << 3;
            let mul_8 = &x * 8;

            assert_mp_eq!(shift_3, mul_8);
        }
    }

    #[test]
    fn shl_rand_large() {
        let mut rng = rand::thread_rng();
        for _ in (0..RAND_ITER) {
            let pow : usize = rng.gen_range(64, 8196);
            let mul_by = Int::from(2).pow(pow);

            let x = rand_int(&mut rng, 10);

            let shift = &x << pow;
            let mul = x * mul_by;

            assert_mp_eq!(shift, mul);
        }
    }

    #[test]
    fn shr_rand() {
        let mut rng = rand::thread_rng();
        for _ in (0..RAND_ITER) {
            let pow : usize = rng.gen_range(64, 8196);
            let x = rand_int(&mut rng, 10);

            let shift_up = &x << pow;
            let shift_down = shift_up >> pow;

            assert_mp_eq!(shift_down, x);
        }
    }

    #[test]
    fn bitand_rand() {
        let mut rng = rand::thread_rng();
        for _ in (0..RAND_ITER) {
            let x = rand_int(&mut rng, 10);
            let y = rand_int(&mut rng, 10);

            let _ = x & y;
        }
    }

    #[test]
    fn hash_rand() {
        let mut rng = rand::thread_rng();
        for _ in (0..RAND_ITER) {
            let x1 = rand_int(&mut rng, 10);
            let x2 = x1.clone();

            assert!(x1 == x2);

            let mut hasher = std::hash::SipHasher::new();
            x1.hash(&mut hasher);
            let x1_hash = hasher.finish();

            let mut hasher = std::hash::SipHasher::new();
            x2.hash(&mut hasher);
            let x2_hash = hasher.finish();

            assert!(x1_hash == x2_hash);
        }
    }

    fn bench_add(b: &mut Bencher, xs: u32, ys: u32) {
        let mut rng = rand::thread_rng();

        let x = rand_int(&mut rng, xs);
        let y = rand_int(&mut rng, ys);

        b.iter(|| {
            let z = &x + &y;
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_add_1_1(b: &mut Bencher) {
        bench_add(b, 1, 1);
    }

    #[bench]
    fn bench_add_10_10(b: &mut Bencher) {
        bench_add(b, 10, 10);
    }

    #[bench]
    fn bench_add_100_100(b: &mut Bencher) {
        bench_add(b, 100, 100);
    }

    #[bench]
    fn bench_add_1000_1000(b: &mut Bencher) {
        bench_add(b, 1000, 1000);
    }

    #[bench]
    fn bench_add_1000_10(b: &mut Bencher) {
        bench_add(b, 1000, 10);
    }

    fn bench_mul(b: &mut Bencher, xs: u32, ys: u32) {
        let mut rng = rand::thread_rng();

        let x = rand_int(&mut rng, xs);
        let y = rand_int(&mut rng, ys);

        b.iter(|| {
            let z = &x * &y;
            test::black_box(z);
        });
    }

    fn bench_pow(b: &mut Bencher, xs: u32, ys: usize) {
        let mut rng = rand::thread_rng();

        let x = rand_int(&mut rng, xs);
        let y : usize = rng.gen_range(0, ys);

        b.iter(|| {
            let z = &x.pow(y);
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_mul_1_1(b: &mut Bencher) {
        bench_mul(b, 1, 1);
    }

    #[bench]
    fn bench_mul_10_10(b: &mut Bencher) {
        bench_mul(b, 10, 10);
    }

    #[bench]
    fn bench_mul_2_20(b: &mut Bencher) {
        bench_mul(b, 2, 20);
    }

    #[bench]
    fn bench_mul_50_50(b: &mut Bencher) {
        bench_mul(b, 50, 50);
    }

    #[bench]
    fn bench_mul_5_50(b: &mut Bencher) {
        bench_mul(b, 5, 50);
    }

    #[bench]
    fn bench_mul_250_250(b: &mut Bencher) {
        bench_mul(b, 250, 250);
    }

    #[bench]
    fn bench_mul_1000_1000(b: &mut Bencher) {
        bench_mul(b, 1000, 1000);
    }

    #[bench]
    fn bench_mul_50_1500(b: &mut Bencher) {
        bench_mul(b, 50, 1500);
    }

    #[bench]
    fn bench_pow_1_1(b: &mut Bencher) {
        bench_pow(b, 1, 1);
    }

    #[bench]
    fn bench_pow_10_10(b: &mut Bencher) {
        bench_pow(b, 10, 10);
    }

    #[bench]
    fn bench_pow_2_20(b: &mut Bencher) {
        bench_pow(b, 2, 20);
    }

    #[bench]
    fn bench_pow_50_50(b: &mut Bencher) {
        bench_pow(b, 50, 50);
    }

    #[bench]
    fn bench_pow_5_50(b: &mut Bencher) {
        bench_mul(b, 5, 50);
    }

    #[bench]
    fn bench_pow_250_250(b: &mut Bencher) {
        bench_mul(b, 250, 250);
    }

    #[bench]
    fn bench_pow_1000_1000(b: &mut Bencher) {
        bench_mul(b, 1000, 1000);
    }

    #[bench]
    fn bench_pow_50_1500(b: &mut Bencher) {
        bench_mul(b, 50, 1500);
    }

    #[bench]
    fn bench_factorial_100(b: &mut Bencher) {
        b.iter(|| {
            let mut i = Int::from(1);

            for j in 2..100 {
                i = i * j;
            }

            i = i * 100;
            test::black_box(i);
        });
    }

    #[bench]
    fn bench_factorial_1000(b: &mut Bencher) {
        b.iter(|| {
            let mut i = Int::from(1);

            for j in 2..1000 {
                i = i * j;
            }

            i = i * 1000;

            test::black_box(i);
        });
    }

    fn bench_div(b: &mut Bencher, xs: u32, ys: u32) {
        let mut rng = rand::thread_rng();

        let x = rand_int(&mut rng, xs);
        let y = rand_int(&mut rng, ys);

        b.iter(|| {
            let z = &x / &y;
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_div_1_1(b: &mut Bencher) {
        bench_div(b, 1, 1);
    }

    #[bench]
    fn bench_div_10_10(b: &mut Bencher) {
        bench_div(b, 10, 10);
    }

    #[bench]
    fn bench_div_20_2(b: &mut Bencher) {
        bench_div(b, 20, 2);
    }

    #[bench]
    fn bench_div_50_50(b: &mut Bencher) {
        bench_div(b, 50, 50);
    }

    #[bench]
    fn bench_div_50_5(b: &mut Bencher) {
        bench_div(b, 50, 5);
    }

    #[bench]
    fn bench_div_250_250(b: &mut Bencher) {
        bench_div(b, 250, 250);
    }

    #[bench]
    fn bench_div_1000_1000(b: &mut Bencher) {
        bench_div(b, 1000, 1000);
    }
}
