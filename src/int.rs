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
use std::fmt;
use std::ops::{
    Add, Sub, Mul, Div, Rem,
    Neg
};
use std::str::FromStr;

use ll;
use ll::limb::{BaseInt, Limb};
use mem;

/**
 * An arbitrary-precision signed integer.
 *
 * This type grows to the size it needs to in order to store the result of any operation.
 *
 * You can convert to a primitive integer type by using `From`: `i32::from(&myint)`.
 */
pub struct Int {
    ptr: *mut Limb,
    size: i32,
    cap: u32
}

impl Int {
    /// Creates a zero-value Int
    pub fn zero() -> Int {
        Int {
            ptr: std::ptr::null_mut(),
            size: 0,
            cap: 0
        }
    }

    /// Creates a new Int from the given Limb.
    pub fn from_single_limb(limb: Limb) -> Int {
        let mut i = Int::with_capacity(1);
        unsafe {
            *i.ptr = limb;
        }
        i.size = 1;

        i
    }

    fn with_capacity(cap: u32) -> Int {
        unsafe {
            let ptr = mem::allocate(cap as usize);
            Int {
                ptr: ptr,
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
            return unsafe { *self.ptr };
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
                ll::cmp(self.ptr, other.ptr, self.abs_size())
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
            let old_ptr = self.ptr as *mut u8;
            let old_cap = (self.cap as usize) * std::mem::size_of::<Limb>();
            let new_cap = size * std::mem::size_of::<Limb>();

            let new_ptr = mem::reallocate(old_ptr, old_cap, new_cap);
            self.ptr = new_ptr as *mut Limb;
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
            ll::base::num_base_digits(self.ptr, size, base as u32)
        };

        let mut buf : Vec<u8> = Vec::with_capacity(num_digits);

        unsafe {
            let bufp = buf.as_mut_ptr();
            let num = ll::base::to_base(bufp, base as u32, self.ptr, size);
            buf.set_len(num);
        }

        let letter = if upper { b'A' } else { b'a' };
        for c in &mut buf {
            if *c < 10 {
                *c = *c + b'0';
            } else {
                *c = (*c - 10) + letter;
            }
        }

        let mut s = unsafe {
            String::from_utf8_unchecked(buf)
        };

        if self.sign() == -1 {
            s.insert(0, '-');
        }

        return s;
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
            let size = ll::base::from_base(i.ptr, buf.as_ptr(), buf.len() as i32, base as u32);
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
        let out_size = if self.abs_size() < other.abs_size() {
            1
        } else {
            (self.abs_size() - other.abs_size()) + 1
        };

        let out_sign = self.sign() * other.sign();
        let mut q = Int::with_capacity(out_size as u32);
        q.size = out_size * out_sign;

        let mut r = Int::with_capacity(other.abs_size() as u32);
        r.size = other.size;

        unsafe {
            ll::divrem(q.ptr, r.ptr,
                       self.ptr, self.abs_size(),
                       other.ptr, other.abs_size());
        }

        q.adjust_size();
        r.adjust_size();

        (q, r)
    }

    fn ensure_capacity(&mut self, cap: u32) {
        if cap > self.cap {
            unsafe {

                let new_ptr = if self.cap > 0 {
                    let old_ptr = self.ptr as *mut u8;
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

                self.ptr = new_ptr;
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
    fn adjust_size(&mut self) {
        if self.size == 0 { true; }
        let sign = self.sign();
        unsafe {
            while self.size != 0 &&
                *self.ptr.offset((self.abs_size() - 1) as isize) == 0 {

                self.size -= sign;
            }
        }
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

        let mut new = Int::with_capacity(self.abs_size() as u32);
        unsafe {
            ll::copy_incr(self.ptr, new.ptr, self.abs_size());
        }
        new.size = self.size;
        new
    }

    fn clone_from(&mut self, other: &Int) {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());

        self.ensure_capacity(other.abs_size() as u32);
        unsafe {
            ll::copy_incr(other.ptr, self.ptr, other.abs_size());
            self.size = other.size;
        }
    }
}

impl Drop for Int {
    fn drop(&mut self) {
        if self.cap > 0 {
            unsafe {
                let ptr = self.ptr as *mut u8;
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
        if self.size == other.size {
            unsafe {
                ll::cmp(self.ptr, other.ptr, self.abs_size()) == Ordering::Equal
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

        self.size == 1 && unsafe { *self.ptr == *other }
    }
}

impl PartialEq<Int> for Limb {
    #[inline]
    fn eq(&self, other: &Int) -> bool {
        other.eq(self)
    }
}

impl Eq for Int { }

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
                (*self.ptr).partial_cmp(other)
            }
        }
    }
}

impl PartialOrd<Int> for Limb {
    #[inline]
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(match other.partial_cmp(self).unwrap() {
            Ordering::Equal => Ordering::Equal,
            Ordering::Less => Ordering::Greater,
            Ordering::Greater => Ordering::Less
        })
    }
}

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
                    ll::cmp(self.ptr, other.ptr, self.abs_size())
                } else {
                    ll::cmp(other.ptr, self.ptr, self.abs_size())
                }
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
                *self.ptr = other;
                self.size = 1;
            }
            return self;
        }
        // `self` is non-zero, reuse the storage for the result.
        unsafe {
            let sign = self.sign();
            let size = self.abs_size();
            let ptr = self.ptr;

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
            // There's a restriction that x-size >= y-size, we can swap the operands
            // no problem, but we'd like to re-use `self`s memory if possible, so
            // if `self` is the smaller of the two we make sure it has enough space
            // for the result
            let (xp, xs, yp, ys) = if self.abs_size() >= other.abs_size() {
                (self.ptr, self.abs_size(), other.ptr, other.abs_size())
            } else {
                self.ensure_capacity(other.abs_size() as u32);
                (other.ptr, other.abs_size(), self.ptr, self.abs_size())
            };

            unsafe {
                let carry = ll::add(self.ptr,
                                    xp, xs,
                                    yp, ys);
                self.size = xs * sign;
                self.adjust_size();

                if carry != 0 {
                    self.push(carry);
                }

                return self;
            }
        } else {
            // Signs are different, use the sign from the bigger (absolute value)
            // of the two numbers and subtract the smaller one.

            let (xp, xs, yp, ys) = if self.abs_size() > other.abs_size() {
                (self.ptr, self.size, other.ptr, other.size)
            } else if self.abs_size() < other.abs_size() {
                self.ensure_capacity(other.abs_size() as u32);
                (other.ptr, other.size, self.ptr, self.size)
            } else {
                match self.abs_cmp(other) {
                    Ordering::Equal => {
                        // They're equal, but opposite signs, so the result
                        // will be zero, clear `self` and return it
                        self.size = 0;
                        return self;
                    }
                    Ordering::Greater =>
                        (self.ptr, self.size, other.ptr, other.size),
                    Ordering::Less =>
                        (other.ptr, other.size, self.ptr, self.size)
                }
            };

            unsafe {
                let _borrow = ll::sub(self.ptr,
                                      xp, xs.abs(),
                                      yp, ys.abs());
                // There shouldn't be any borrow
                debug_assert!(_borrow == 0);

                self.size = xs;
                self.adjust_size();
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
                *self.ptr = other;
                self.size = -1;
            }
            return self;
        }
        // `self` is non-zero, reuse the storage for the result.
        unsafe {
            let sign = self.sign();
            let size = self.abs_size();
            let ptr = self.ptr;

            // Self is negative, just "add" `other`
            if sign == -1 {
                let carry = ll::add_1(ptr, ptr, size, other);
                if carry != 0 {
                    self.push(carry);
                }
            } else {
                // Self is positive, subtract other from self
                let carry = ll::sub_1(ptr, ptr, size, other);
                self.adjust_size();
                if carry != 0 {
                    // There was a carry, ignore it but flip the sign on self
                    self.size = -self.abs_size();
                }
            }
        }

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
            // Signs are the same, subtract the smaller one from
            // the bigger one and adjust the sign as appropriate
            let (xp, xs, yp, ys, flip) = match self.abs_cmp(other) {
                Ordering::Equal => {
                    // x - x, just return zero
                    self.size = 0;
                    return self;
                }
                Ordering::Less => {
                    self.ensure_capacity(other.abs_size() as u32);
                    (other.ptr, other.size, self.ptr, self.size, true)
                }
                Ordering::Greater =>
                    (self.ptr, self.size, other.ptr, other.size, false)
            };

            unsafe {
                let _borrow = ll::sub(self.ptr, xp, xs.abs(), yp, ys.abs());
                debug_assert!(_borrow == 0);
                self.size = if flip {
                    xs * -1
                } else {
                    xs
                };
            }

            return self;
        } else { // Different signs
            if self.sign() == -1 {
                // self is negative, use addition and negation
                let res = (-self) + other;
                return -res;
            } else {
                // Other is negative, handle as addition
                let (xp, xs, yp, ys) = if self.abs_size() >= other.abs_size() {
                    (self.ptr, self.abs_size(), other.ptr, other.abs_size())
                } else {
                    self.ensure_capacity(other.abs_size() as u32);
                    (other.ptr, other.abs_size(), self.ptr, self.abs_size())
                };

                unsafe {
                    let carry = ll::add(self.ptr, xp, xs, yp, ys);
                    self.size = xs;
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
            return -other;
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
        if other == 0 || self.sign() == 0 {
            self.size = 0;
            return self;
        }

        if other == 1 {
            return self;
        }

        unsafe {
            let carry = ll::mul_1(self.ptr, self.ptr, self.abs_size(), other);
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
                let mut ret = other.clone() * *self.ptr;
                let size = ret.abs_size();
                ret.size = size * out_sign;
                return ret;
            }
        }
        if other.abs_size() == 1 {
            unsafe {
                let mut ret = self.clone() * *other.ptr;
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
                (self.ptr, self.abs_size(), other.ptr, other.abs_size())
            } else {
                (other.ptr, other.abs_size(), self.ptr, self.abs_size())
            };
            ll::mul(out.ptr, xp, xs, yp, ys);

            // Top limb may be zero
            out.adjust_size();
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
                let mut out = self * *other.ptr;
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
            let val = unsafe { *self.ptr };
            let mut out = other * val;
            out.size *= self.sign();
            return out;
        }
        if other.abs_size() == 1 {
            let val = unsafe { *other.ptr };
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
        if other == 0 {
            ll::divide_by_zero();
        }
        if other == 1 || self.sign() == 0 {
            return self;
        }

        unsafe {
            // Ignore the remainder
            ll::divrem_1(self.ptr, 0, self.ptr, self.abs_size(), other);
            // Adjust the size if necessary
            self.adjust_size();
        }

        return self;
    }
}

impl<'a, 'b> Div<&'a Int> for &'b Int {
    type Output = Int;

    fn div(self, other: &'a Int) -> Int {
        if other.sign() == 0 {
            ll::divide_by_zero();
        }
        if other.abs_size() == 1 {
            let l = unsafe { *other.ptr };
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
        if other == 0 {
            ll::divide_by_zero();
        }
        // x % 1 == 0, 0 % n == 0
        if other == 1 || self.sign() == 0 {
            self.size = 0;
            return self;
        }

        unsafe {
            let rem = ll::divrem_1(self.ptr, 0, self.ptr, self.abs_size(), other);
            // Reuse the space from `self`, taking the sign from the numerator
            // Since `rem` has to satisfy `N = QD + R` and D is always positive,
            // `R` will always be the same sign as the numerator.
            *self.ptr = rem;
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
        if other.sign() == 0 {
            ll::divide_by_zero();
        }
        if other.abs_size() == 1 {
            let l = unsafe { *other.ptr };
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
                return *self.ptr == (other.abs() as BaseInt);
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
                if ::std::mem::size_of::<BaseInt>() > ::std::mem::size_of::<$t>() {
                    // Handle conversion where BaseInt = u32 and $t = i64
                    if i.abs_size() >= 2 { // Fallthrough if there's only one limb
                        let mask = !0 >> 1;
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
                if ::std::mem::size_of::<BaseInt>() > ::std::mem::size_of::<$t>() {
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

#[cfg(test)]
mod test {
    use super::*;
    use std::str::FromStr;

    #[test]
    fn from_string_10() {
        let cases = [
            ("0",        0i32),
            ("123456",   123456),
            ("0123",     123),
            ("000000",   0),
            ("-0",       0),
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

            assert_eq!(l + r, a);
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

            assert_eq!(l - r, a);
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

            assert_eq!(l * r, a);
        }
    }

    #[test]
    fn div() {
        let cases = [
            ("1", "1", "1"),
            ("1234", "-1", "-1234"),
            ("8", "9", "0"),
            ("-9", "-3", "3"),
            ("1234567891011121314151617", "9876543210123", "124999998961"),
            ("-1234567891011121314151617", "9876543210123", "-124999998961"),
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            assert_eq!(l / r, a);
        }
    }
}
