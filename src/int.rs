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
use std::{io, mem, fmt, hash};
use std::num::Zero;
use std::ops::{
    Add, Sub, Mul, Div, Rem, Neg,
    AddAssign, SubAssign, MulAssign, DivAssign, RemAssign,
    Shl, Shr, BitAnd, BitOr, BitXor,
    ShlAssign, ShrAssign, BitAndAssign, BitOrAssign, BitXorAssign,
};
use std::ptr::Unique;
use std::str::FromStr;
use rand::Rng;

use hamming;
use alloc;

use ll;
use ll::limb::{BaseInt, Limb};
use ll::limb_ptr::{Limbs, LimbsMut};

use alloc::raw_vec::RawVec;

use traits::DivRem;

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
 * while the remainder/modulo operator returns `R`. The sign of `R` is the same as the sign of `Q`.
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

    /**
     * Views the internal memory as a `RawVec`, which can be
     * manipulated to change `self`'s allocation.
     */
    fn with_raw_vec<F: FnOnce(&mut RawVec<Limb>)>(&mut self, f: F) {
        unsafe {
            let old_cap = self.cap as usize;
            let mut vec = RawVec::from_raw_parts(self.ptr.get_mut(), old_cap);
            // if `f` panics, let `vec` do the cleaning up, not self.
            self.cap = 0;

            f(&mut vec);

            // update `self` for any changes that happened
            self.ptr = Unique::new(vec.ptr());
            let new_cap = vec.cap();
            assert!(new_cap <= std::u32::MAX as usize);
            self.cap = new_cap as u32;
            // ownership has transferred back into `self`, so make
            // sure that allocation isn't freed by `vec`.
            std::mem::forget(vec);

            if old_cap < new_cap {
                // the allocation got larger, new Limbs should be
                // zero.
                let self_ptr = self.limbs_uninit();
                std::ptr::write_bytes(&mut *self_ptr.offset(old_cap as isize) as *mut _ as *mut u8,
                                      0,
                                      (new_cap - old_cap) * std::mem::size_of::<Limb>());
            }
        }
    }

    fn with_capacity(cap: u32) -> Int {
        let mut ret = Int::zero();
        if cap != 0 {
            ret.with_raw_vec(|v| v.reserve_exact(0, cap as usize))
        }
        ret
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
                ll::cmp(self.limbs(), other.limbs(), self.abs_size())
            }
        }
    }

    /**
     * Returns the equality of the absolute values of self and
     * other.
     */
    pub fn abs_eq(&self, other: &Int) -> bool {
        self.abs_cmp(other) == Ordering::Equal
    }

    /**
     * Hashes the value without including the sign, useful for when the
     * sign is handled elsewhere and making a copy just to change the sign
     * is wasteful
     */
    pub fn abs_hash<H>(&self, state: &mut H) where H: hash::Hasher {
        use std::hash::Hash;
        let mut size = self.abs_size();
        unsafe {
            let mut ptr = self.limbs();
            while size > 0 {
                let l = *ptr;
                l.hash(state);

                ptr = ptr.offset(1);
                size -= 1;
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

        self.with_raw_vec(|v| {
            v.shrink_to_fit(size);
        })
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
        let mut num_digits = unsafe {
            ll::base::num_base_digits(self.limbs(), size - 1, base as u32)
        };

        if self.sign() == -1 {
            num_digits += 1;
        }

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
            ll::base::to_base(base as u32, self.limbs(), size, |b| {
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
            let size = ll::base::from_base(i.limbs_uninit(), buf.as_ptr(), buf.len() as i32, base as u32);
            i.size = (size as i32) * sign;
        }

        Ok(i)
    }

    /**
     * Divide self by other, returning the quotient, Q, and remainder, R as (Q, R).
     *
     * With N = self, D = other, Q and R satisfy: `N = QD + R`.
     * The sign of `Q` and `R` are the same.
     *
     * This will panic if `other` is zero.
     */
    pub fn divmod(&self, other: &Int) -> (Int, Int) {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());
        if other.sign() == 0 {
            ll::divide_by_zero();
        }
        if self.sign() == 0 {
            return (self.clone(), Int::zero())
        }

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
            ll::divrem(q.limbs_mut(), r.limbs_mut(),
                       self.limbs(), self.abs_size(),
                       other.limbs(), other.abs_size());
        }

        q.normalize();
        r.normalize();

        (q, r)
    }

    /**
     * Raises self to the power of exp
     */
    pub fn pow(&self, exp: usize) -> Int {
        debug_assert!(self.well_formed());
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

                let ret_sz = unsafe {
                    ll::pow::num_pow_limbs(self.limbs(), self.abs_size(), exp as u32)
                };
                let mut ret = Int::with_capacity(ret_sz as u32);
                ret.size = ret_sz * signum;

                unsafe {
                    ll::pow::pow(ret.limbs_mut(), self.limbs(), self.abs_size(), exp as u32);
                }

                ret.normalize();

                ret
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
            let sz = self.abs_size() * 2;
            let mut ret = Int::with_capacity(sz as u32);
            ret.size = sz;
            unsafe {
                ll::sqr(ret.limbs_mut(), self.limbs(), self.abs_size());
            }
            ret.normalize();

            ret
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
            self.square()
        }
    }

    /**
     * Compute the sqrt of this number, returning its floor, S,  and the
     * remainder, R, as Some((S, R)), or None if this number is negative.
     *
     * The numbers S, R are both positive and satisfy `self = S * S +
     * R`.
     */
    pub fn sqrt_rem(mut self) -> Option<(Int, Int)> {
        debug_assert!(self.well_formed());

        if self.sign() < 0 {
            return None
        }

        // the floor of a (correctly rounded) f64 sqrt gives the right
        // answer, until this number (it is 67108865**2 - 1, but
        // f64::sqrt is rounded *up* to 67108865 precisely).
        if self < 4_503_599_761_588_224_u64 {
            let this = u64::from(&self);
            let sqrt = (this as f64).sqrt().floor() as u64;
            let rem = this - sqrt * sqrt;

            // reuse the memory
            self.size = 0;
            self.push(Limb(sqrt as BaseInt));
            self.normalize();

            Some((self,
                  Int::from(rem)))
        } else {
            let n = self.bit_length();
            let l = (n as usize - 1) / 4;
            assert!(l > 0);

            let mask = (Int::from(1) << l) - 1;
            let low = &self & &mask;
            self >>= l;
            let mut middle = &self & mask;
            self >>= l;
            let (high_sqrt, mut high_rem) = self.sqrt_rem().unwrap();

            high_rem <<= l;
            middle |= high_rem;
            let (q, u) = middle.divmod(&(&high_sqrt << 1));

            let mut s = (high_sqrt << l) + &q;
            let mut r = (u << l) + low - q.dsquare();

            if r < 0 {
                r += &s << 1;
                r -= 1;
                s -= 1;
            }
            debug_assert!(r >= 0);
            Some((s, r))
        }
    }

    /**
     * Negates `self` in-place
     */
    pub fn negate(&mut self) {
        self.size *= -1;
    }

    /**
     * Returns whether or not this number is even.
     *
     * Returns 0 if `self == 0`
     */
    #[inline]
    pub fn is_even(&self) -> bool {
        debug_assert!(self.well_formed());
        (self.to_single_limb().0 & 1) == 0
    }

    /**
     * Returns the number of trailing zero bits in this number
     *
     * Returns 0 if `self == 0`
     */
    #[inline]
    pub fn trailing_zeros(&self) -> u32 {
        debug_assert!(self.well_formed());
        if self.sign() == 0 {
            0
        } else {
            unsafe {
                ll::scan_1(self.limbs(), self.abs_size())
            }
        }
    }

    /**
     * Returns the number of ones (the population count) in this number
     *
     * If this number is negative, it has infinitely many ones (in
     * two's complement), so this returns usize::MAX.
     */
    pub fn count_ones(&self) -> usize {
        debug_assert!(self.well_formed());
        if self.sign() < 0 {
            std::usize::MAX
        } else {
            let bytes = unsafe {
                std::slice::from_raw_parts(self.ptr.get() as *const _ as *const u8,
                                           self.abs_size() as usize * std::mem::size_of::<Limb>())
            };
            hamming::weight(bytes) as usize
        }
    }

    /**
     * Returns the number of bits required to represent (the absolute
     * value of) this number, that is, `floor(log2(abs(self))) + 1`.
     *
     * Returns 1 if `self == 0`.
     */
    #[inline]
    pub fn bit_length(&self) -> u32 {
        if *self == 0 {
            1
        } else {
            unsafe {
                ll::base::num_base_digits(self.limbs(), self.abs_size(), 2) as u32
            }
        }
    }

    /**
     * Returns the value of the `bit`th bit in this number, as if it
     * were represented in two's complement.
     */
    #[inline]
    pub fn bit(&self, bit: u32) -> bool {
        let word = (bit / Limb::BITS as u32) as isize;
        let subbit = bit % Limb::BITS as u32;
        if word < self.abs_size() as isize {
            let b = unsafe {
                let w: Limb = *self.limbs().offset(word);
                w.0 & (1 << subbit) != 0
            };
            if self.sign() >= 0 {
                b
            } else {
                let first_one = self.trailing_zeros();
                // the number is negative, so, in two's complement,
                // bits up to and including the first one are the same
                // as their sign-magnitude values (... ^ false), while
                // bits beyond that are complemented (... ^ true)
                b ^ (bit > first_one)
            }
        } else {
            // we're beyond the in-memory limbs, so the bits are
            // either all zeros (positive) or all ones (negative)
            self.sign() < 0
        }
    }

    /**
     * Set the `bit`th bit of this number to `bit_val`, treating
     * negative numbers as if they're stored in two's complement.
     */
    pub fn set_bit(&mut self, bit: u32, bit_val: bool) {
        debug_assert!(self.well_formed());
        let word = bit / Limb::BITS as u32;
        let subbit = bit % Limb::BITS as u32;
        let flag = Limb(1 << subbit);

        let sign = self.sign();

        unsafe {

            if word >= self.abs_size() as u32 {
                // the bit is beyond the end, so more space is needed,
                // and we need to be careful to ensure it's all zero
                // because they'll all be part of the number itself
                // used once the bit is set
                self.ensure_capacity(word + 1);

                let size = self.abs_size();
                ll::zero(self.limbs_uninit().offset(size as isize), word as i32 - size + 1);

                self.size = word as i32 + 1;
                if sign < 0 {
                    self.size = -self.size
                }
            }

            if sign < 0 {
                // this could probably be replaced by something
                // similar to what `bit` does
                self.negate_twos_complement();
            }

            let mut ptr = self.limbs_mut().offset(word as isize);
            let val = if bit_val {
                *ptr | flag
            } else {
                *ptr & !flag
            };
            *ptr = val;

            if sign < 0 {
                // put self back to normal
                self.negate_twos_complement();
            }
        }
        self.normalize()
    }

    // get a Limbs to all limbs currently initialised/in use
    fn limbs(&self) -> Limbs {
        unsafe {
            Limbs::new(self.ptr.get(), 0, self.abs_size())
        }
    }
    // get a LimbsMut to all limbs currently initialised/in use
    fn limbs_mut(&mut self) -> LimbsMut {
        unsafe {
            LimbsMut::new(self.ptr.get_mut(), 0, self.abs_size())
        }
    }
    // get a LimbsMut to all allocated limbs
    unsafe fn limbs_uninit(&mut self) -> LimbsMut {
        LimbsMut::new(self.ptr.get_mut(), 0, self.cap as i32)
    }

    fn ensure_capacity(&mut self, cap: u32) {
        if cap > self.cap {
            let old_cap = self.cap as usize;
            self.with_raw_vec(|v| {
                v.reserve_exact(old_cap, cap as usize - old_cap)
            })
        }
    }

    fn push(&mut self, limb: Limb) {
        let new_size = (self.abs_size() + 1) as u32;
        self.ensure_capacity(new_size);
        unsafe {
            let pos = self.abs_size();
            *self.limbs_uninit().offset(pos as isize) = limb;
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
        if self.size == 0 { return }
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

    /**
     * convert self into two's complement format (i.e. *self =
     * (!*self) + 1)
     */
    fn negate_twos_complement(&mut self) {
        unsafe {
            let self_ptr = self.limbs_mut();
            let carry = ll::twos_complement(self_ptr, self_ptr.as_const(), self.abs_size());
            if carry != 0 {
                self.push(carry)
            }
        }
        self.size = -self.size;
    }

    /// Calculates the Greatest Common Divisor (GCD) of the number and `other`.
    ///
    /// The result is always positive.
    #[inline]
    pub fn gcd(&self, other: &Int) -> Int {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());

        let (mut a, mut b) = if self.abs_size() >= other.abs_size() {
            ((*self).clone(), (*other).clone())
        } else {
            ((*other).clone(), (*self).clone())
        };

        if a == Int::zero() {
            return b;
        }

        if b == Int::zero() {
            return a;
        }

        let out_size = a.abs_size();
        let mut r = Int::with_capacity(out_size as u32);
        r.size = out_size;

        unsafe {
            ll::gcd(r.limbs_mut(), a.limbs_mut(), a.abs_size(), b.limbs_mut(), b.abs_size());
            r.normalize();
            r
        }
    }

    /// Calculates the Lowest Common Multiple (LCM) of the number and `other`.
    #[inline]
    pub fn lcm(&self, other: &Int) -> Int {
        (self * other).abs() / self.gcd(other)
    }

    pub fn to_f64(&self) -> f64 {
        let sz = self.abs_size();
        if sz == 0 {
            return 0.0;
        }

        let mut highest_limb = unsafe {
            *self.limbs().offset((sz - 1) as isize)
        };
        let leading_zeros = highest_limb.leading_zeros();
        let mut shifted = 0;
        if leading_zeros > 11 && sz > 1 {
            highest_limb = highest_limb << leading_zeros;
            let next_limb = unsafe {
                *self.limbs().offset((sz - 2) as isize)
            };

            highest_limb = highest_limb | (next_limb >> (Limb::BITS - leading_zeros as usize));
            shifted = leading_zeros;
        }

        let exp = ((sz - 1) * Limb::BITS as i32) - shifted as i32;

        let f = highest_limb.0 as f64;
        let exp = (2.0f64).powi(exp);
        f * exp
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
            ll::copy_incr(self.limbs(), new.limbs_uninit(), self.abs_size());
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
            ll::copy_incr(other.limbs(), self.limbs_uninit(), other.abs_size());
            self.size = other.size;
        }
    }
}

impl std::default::Default for Int {
    #[inline]
    fn default() -> Int {
        Int::zero()
    }
}

impl Drop for Int {
    fn drop(&mut self) {
        if self.cap > 0 {
            unsafe {
                drop(RawVec::from_raw_parts(self.ptr.get_mut(),
                                            self.cap as usize));
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
                ll::cmp(self.limbs(), other.limbs(), self.abs_size()) == Ordering::Equal
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

        self.size == 1 && *self.limbs() == *other
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
                    ll::cmp(self.limbs(), other.limbs(), self.abs_size())
                } else {
                    ll::cmp(other.limbs(), self.limbs(), self.abs_size())
                }
            }
        }
    }
}

impl PartialOrd<Int> for Int {
    #[inline]
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
            (*self.limbs()).partial_cmp(other)
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
        self.abs_hash(state);
    }
}

impl AddAssign<Limb> for Int {
    fn add_assign(&mut self, other: Limb) {
        debug_assert!(self.well_formed());
        if other == 0 { return; }

        // No capacity means `self` is zero. Just push `other` into it
        if self.cap == 0 {
            self.push(other);
            return;
        }
        // This is zero, but has allocated space, so just store `other`
        if self.size == 0 {
            unsafe {
                *self.limbs_uninit() = other;
                self.size = 1;
                return
            }
        }
        // `self` is non-zero, reuse the storage for the result.
        unsafe {
            let sign = self.sign();
            let size = self.abs_size();
            let ptr = self.limbs_mut();

            // Self is positive, just add `other`
            if sign == 1 {
                let carry = ll::add_1(ptr, ptr.as_const(), size, other);
                if carry != 0 {
                    self.push(carry);
                }
            } else {
                // Self is negative, "subtract" other from self, basically doing:
                // -(-self - other) == self + other
                let borrow = ll::sub_1(ptr, ptr.as_const(), size, other);
                if borrow != 0 {
                    // There was a borrow, ignore it but flip the sign on self
                    self.size = self.abs_size();
                }
                self.normalize();
            }
        }
    }
}

impl Add<Limb> for Int {
    type Output = Int;

    #[inline]
    fn add(mut self, other: Limb) -> Int {
        self += other;
        self
    }
}

impl<'a> AddAssign<&'a Int> for Int {
    fn add_assign(&mut self, other: &'a Int) {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());

        if self.sign() == 0 {
            // Try to reuse the allocation from `self`
            self.clone_from(other);
            return;
        }
        if other.sign() == 0 {
            return;
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
                let (xp, xs, yp, ys) = if self.abs_size() >= other.abs_size() {
                    (self.limbs(), self.abs_size(), other.limbs(), other.abs_size())
                } else {
                    self.ensure_capacity(other.abs_size() as u32);
                    (other.limbs(), other.abs_size(), self.limbs(), self.abs_size())
                };

                // Fetch the pointer first to make completely sure the compiler
                // won't make bogus claims about nonaliasing due to the &mut
                let ptr = self.limbs_uninit();

                let carry = ll::add(ptr,
                                    xp, xs,
                                    yp, ys);
                self.size = xs * sign;
                if carry != 0 {
                    self.push(carry);
                }
                self.normalize();
            }
        } else {
            // Signs are different, use the sign from the bigger (absolute value)
            // of the two numbers and subtract the smaller one.

            unsafe {
                let (xp, xs, yp, ys) = if self.abs_size() > other.abs_size() {
                    (self.limbs(), self.size, other.limbs(), other.size)
                } else if self.abs_size() < other.abs_size() {
                    self.ensure_capacity(other.abs_size() as u32);
                    (other.limbs(), other.size, self.limbs(), self.size)
                } else {
                    match self.abs_cmp(other) {
                        Ordering::Equal => {
                            // They're equal, but opposite signs, so the result
                            // will be zero, clear `self` and return
                            self.size = 0;
                            return;
                        }
                        Ordering::Greater =>
                            (self.limbs(), self.size, other.limbs(), other.size),
                        Ordering::Less =>
                            (other.limbs(), other.size, self.limbs(), self.size)
                    }
                };

                // Fetch the pointer first to make completely sure the compiler
                // won't make bogus claims about nonaliasing due to the &mut
                let ptr = self.limbs_uninit();

                let _borrow = ll::sub(ptr,
                                      xp, xs.abs(),
                                      yp, ys.abs());
                // There shouldn't be any borrow
                debug_assert!(_borrow == 0);

                self.size = xs;
                self.normalize();
                debug_assert!(self.abs_size() > 0);
            }
        }
    }
}

impl<'a> Add<&'a Int> for Int {
    type Output = Int;

    #[inline]
    fn add(mut self, other: &'a Int) -> Int {
        self += other;
        self
    }
}

impl<'a> Add<Int> for &'a Int {
    type Output = Int;

    #[inline]
    fn add(self, other: Int) -> Int {
        // Forward to other + self
        other.add(self)
    }
}

impl Add<Int> for Int {
    type Output = Int;

    #[inline]
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

impl AddAssign<Int> for Int {
    #[inline]
    fn add_assign(&mut self, mut other: Int) {
        // Use the allocation of the larger of the two inputs.
        // Doing the obvious and simply swapping self and other
        // when other.size > self.size results in poor codegen.
        if other.abs_size() > self.abs_size() {
            // Instead we doing the addition in-place, then overwrite
            // self with other. This results in better codegen and better
            // memory allocation behaviour.
            other += &*self;
            *self = other;
        } else {
            *self += &other;
        }
    }
}

impl<'a, 'b> Add<&'a Int> for &'b Int {
    type Output = Int;

    #[inline]
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

impl SubAssign<Limb> for Int {
    fn sub_assign(&mut self, other: Limb) {
        debug_assert!(self.well_formed());
        if other == 0 { return; }

        // No capacity means `self` is zero. Just push the limb.
        if self.cap == 0 {
            self.push(other);
            self.size = -1;
            return;
        }
        // This is zero, but has allocated space, so just store `other`
        if self.size == 0 {
            unsafe {
                *self.limbs_uninit() = other;
                self.size = -1;
            }
            return;
        }
        // `self` is non-zero, reuse the storage for the result.
        unsafe {
            let sign = self.sign();
            let size = self.abs_size();
            let ptr = self.limbs_mut();

            // Self is negative, just "add" `other`
            if sign == -1 {
                let carry = ll::add_1(ptr, ptr.as_const(), size, other);
                if carry != 0 {
                    self.push(carry);
                }
            } else {
                // Self is positive, subtract other from self
                let carry = ll::sub_1(ptr, ptr.as_const(), size, other);
                self.normalize();
                if carry != 0 {
                    // There was a carry, and the native operations
                    // work with two's complement, so we need to get
                    // everything back into sign-magnitude form
                    self.negate_twos_complement()
                }
            }
        }

        debug_assert!(self.well_formed());
    }
}

impl Sub<Limb> for Int {
    type Output = Int;

    #[inline]
    fn sub(mut self, other: Limb) -> Int {
        self -= other;
        self
    }
}

impl<'a> SubAssign<&'a Int> for Int {
    fn sub_assign(&mut self, other: &'a Int) {
        debug_assert!(self.well_formed());
        debug_assert!(other.well_formed());

        // LHS is zero, set self to the negation of the RHS
        if self.sign() == 0 {
            self.clone_from(other);
            self.size *= -1;
            return;
        }
        // RHS is zero, do nothing
        if other.sign() == 0 {
            return;
        }

        if self.sign() == other.sign() {
            unsafe {
                // Signs are the same, subtract the smaller one from
                // the bigger one and adjust the sign as appropriate
                let (xp, xs, yp, ys, flip) = match self.abs_cmp(other) {
                    Ordering::Equal => {
                        // x - x, just return zero
                        self.size = 0;
                        return;
                    }
                    Ordering::Less => {
                        self.ensure_capacity(other.abs_size() as u32);
                        (other.limbs(), other.size, self.limbs(), self.size, true)
                    }
                    Ordering::Greater =>
                        (self.limbs(), self.size, other.limbs(), other.size, false)
                };

                // Fetch the pointer first to make completely sure the compiler
                // won't make bogus claims about nonaliasing due to the &mut
                let ptr = self.limbs_uninit();

                let _borrow = ll::sub(ptr, xp, xs.abs(), yp, ys.abs());
                debug_assert!(_borrow == 0);
                self.size = if flip {
                    xs * -1
                } else {
                    xs
                };
            }

            self.normalize();
        } else { // Different signs
            if self.sign() == -1 {
                // self is negative, use addition and negation
                self.size *= -1;
                *self += other;
                self.size *= -1;
            } else {
                unsafe {
                    // Other is negative, handle as addition
                    let (xp, xs, yp, ys) = if self.abs_size() >= other.abs_size() {
                        (self.limbs(), self.abs_size(), other.limbs(), other.abs_size())
                    } else {
                        self.ensure_capacity(other.abs_size() as u32);
                        (other.limbs(), other.abs_size(), self.limbs(), self.abs_size())
                    };

                    // Fetch the pointer first to make completely sure the compiler
                    // won't make bogus claims about nonaliasing due to the &mut
                    let ptr = self.limbs_uninit();

                    let carry = ll::add(ptr, xp, xs, yp, ys);
                    self.size = xs;
                    if carry != 0 {
                        self.push(carry);
                    }
                    self.normalize();
                }
            }
        }
    }
}

impl<'a> Sub<&'a Int> for Int {
    type Output = Int;

    #[inline]
    fn sub(mut self, other: &'a Int) -> Int {
        self -= other;
        self
    }
}

impl<'a> Sub<Int> for &'a Int {
    type Output = Int;

    #[inline]
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

    #[inline]
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

impl SubAssign<Int> for Int {
    #[inline]
    fn sub_assign(&mut self, other: Int) {
        if other.sign() == 0 {
            return;
        }
        if self.sign() == 0 {
            *self = -other;
            return;
        }
        *self -= &other;
    }
}

impl<'a, 'b> Sub<&'a Int> for &'b Int {
    type Output = Int;

    #[inline]
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

impl MulAssign<Limb> for Int {
    fn mul_assign(&mut self, other: Limb) {
        debug_assert!(self.well_formed());
        if other == 0 || self.sign() == 0 {
            self.size = 0;
            return;
        }

        if other == 1 {
            return;
        }

        unsafe {
            // Fetch the pointer first to make completely sure the compiler
            // won't make bogus claims about nonaliasing due to the &mut

            let carry = ll::mul_1(self.limbs_mut(), self.limbs(), self.abs_size(), other);
            if carry != 0 {
                self.push(carry);
            }
        }
    }
}

impl Mul<Limb> for Int {
    type Output = Int;

    #[inline]
    fn mul(mut self, other: Limb) -> Int {
        self *= other;
        self
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
            let mut ret = other.clone() * *self.limbs();
            let size = ret.abs_size();
            ret.size = size * out_sign;
            return ret;
        }
        if other.abs_size() == 1 {
            let mut ret = self.clone() * *other.limbs();
            let size = ret.abs_size();
            ret.size = size * out_sign;
            return ret;
        }

        let out_size = self.abs_size() + other.abs_size();

        let mut out = Int::with_capacity(out_size as u32);
        out.size = out_size * out_sign;

        unsafe {
            let (xp, xs, yp, ys) = if self.abs_size() >= other.abs_size() {
                (self.limbs(), self.abs_size(), other.limbs(), other.abs_size())
            } else {
                (other.limbs(), other.abs_size(), self.limbs(), self.abs_size())
            };
            ll::mul(out.limbs_mut(), xp, xs, yp, ys);

            // Top limb may be zero
            out.normalize();
            return out;
        }
    }
}

impl<'a> Mul<&'a Int> for Int {
    type Output = Int;

    #[inline]
    fn mul(mut self, other: &'a Int) -> Int {
        // `other` is zero
        if other.sign() == 0 {
            self.size = 0;
            return self;
        }

        // `other` is a single limb, reuse the allocation of self
        if other.abs_size() == 1 {
            let mut out = self * *other.limbs();
            out.size *= other.sign();
            return out;
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
            let val = *self.limbs();
            let mut out = other * val;
            out.size *= self.sign();
            return out;
        }
        if other.abs_size() == 1 {
            let val = *other.limbs();
            let mut out = self * val;
            out.size *= other.sign();
            return out;
        }

        // Still need to allocate for the result, just forward to
        // the by-reference impl
        (&self) * (&other)
    }
}

impl<'a> MulAssign<&'a Int> for Int {
    #[inline]
    fn mul_assign(&mut self, other: &'a Int) {
        if self.sign() == 0 {
            return;
        }
        if other.sign() == 0 {
            self.size = 0;
            return;
        }
        let res = &*self * other;
        *self = res;
    }
}

impl MulAssign<Int> for Int {
    #[inline]
    fn mul_assign(&mut self, other: Int) {
        if self.sign() == 0 {
            return;
        }
        if other.sign() == 0 {
            self.size = 0;
            return;
        }
        let res = &*self * other;
        *self = res;
    }
}

impl DivAssign<Limb> for Int {
    fn div_assign(&mut self, other: Limb) {
        debug_assert!(self.well_formed());
        if other == 0 {
            ll::divide_by_zero();
        }
        if other == 1 || self.sign() == 0 {
            return;
        }

        unsafe {
            // Ignore the remainder
            ll::divrem_1(self.limbs_mut(), 0, self.limbs(), self.abs_size(), other);
            // Adjust the size if necessary
            self.normalize();
        }
    }
}

impl Div<Limb> for Int {
    type Output = Int;

    #[inline]
    fn div(mut self, other: Limb) -> Int {
        self /= other;
        self
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
            let l = *other.limbs();
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

    #[inline]
    fn div(self, other: &'a Int) -> Int {
        (&self) / other
    }
}

impl<'a> Div<Int> for &'a Int {
    type Output = Int;

    #[inline]
    fn div(self, other: Int) -> Int {
        self / (&other)
    }
}

impl Div<Int> for Int {
    type Output = Int;

    #[inline]
    fn div(self, other: Int) -> Int {
        (&self) / (&other)
    }
}

impl<'a> DivAssign<&'a Int> for Int {
    #[inline]
    fn div_assign(&mut self, other: &'a Int) {
        let res = &*self / other;
        *self = res;
    }
}

impl DivAssign<Int> for Int {
    #[inline]
    fn div_assign(&mut self, other: Int) {
        let res = &*self / other;
        *self = res;
    }
}

impl Rem<Limb> for Int {
    type Output = Int;

    #[inline]
    fn rem(mut self, other: Limb) -> Int {
        self %= other;
        self
    }
}

impl RemAssign<Limb> for Int {
    fn rem_assign(&mut self, other: Limb) {
        debug_assert!(self.well_formed());
        if other == 0 {
            ll::divide_by_zero();
        }
        // x % 1 == 0, 0 % n == 0
        if other == 1 || self.sign() == 0 {
            self.size = 0;
            return;
        }

        unsafe {
            let rem = ll::divrem_1(self.limbs_mut(), 0, self.limbs(), self.abs_size(), other);
            // Reuse the space from `self`, taking the sign from the numerator
            // Since `rem` has to satisfy `N = QD + R` and D is always positive,
            // `R` will always be the same sign as the numerator.
            *self.limbs_mut() = rem;
            let sign = self.sign();
            self.size = sign;

            self.normalize();

            if self.cap > 8 {
                // Shrink self, since it's at least 8 times bigger than necessary
                self.shrink_to_fit();
            }

        }
    }
}

impl DivRem<Limb> for Int {
    type Output = (Int, Limb);

    fn divrem(mut self, other: Limb) -> Self::Output {
        debug_assert!(self.well_formed());
        if other == 0 {
            ll::divide_by_zero();
        }
        // x % 1 == 0, 0 % n == 0
        if other == 1 || self.sign() == 0 {
            self.size = 0;
            return (self, Limb(0));
        }

        let rem = unsafe { ll::divrem_1(self.limbs_mut(), 0, self.limbs(), self.abs_size(), other) };
        self.normalize();
        return (self, rem);
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
            let l = *other.limbs();
            return self.clone() % l;
        }

        self.divmod(other).1
    }
}

impl<'a> Rem<&'a Int> for Int {
    type Output = Int;

    #[inline]
    fn rem(self, other: &'a Int) -> Int {
        (&self) % other
    }
}

impl<'a> Rem<Int> for &'a Int {
    type Output = Int;

    #[inline]
    fn rem(self, other: Int) -> Int {
        self % (&other)
    }
}

impl Rem<Int> for Int {
    type Output = Int;

    #[inline]
    fn rem(self, other: Int) -> Int {
        (&self) % (&other)
    }
}

impl<'a, 'b> DivRem<&'a Int> for &'b Int {
    type Output = (Int, Int);

    #[inline]
    fn divrem(self, other: &'a Int) -> (Int, Int) {
        self.divmod(other)
    }
}

impl RemAssign<Int> for Int {
    #[inline]
    fn rem_assign(&mut self, other: Int) {
        let res = &*self % other;
        *self = res;
    }
}
impl<'a> RemAssign<&'a Int> for Int {
    #[inline]
    fn rem_assign(&mut self, other: &'a Int) {
        let res = &*self % other;
        *self = res;
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

impl ShlAssign<usize> for Int {
    #[inline]
    fn shl_assign(&mut self, mut cnt: usize) {
        debug_assert!(self.well_formed());
        if self.sign() == 0 { return; }

        if cnt >= Limb::BITS as usize {
            let extra_limbs = (cnt / Limb::BITS as usize) as u32;
            debug_assert!(extra_limbs >= 1);
            cnt = cnt % Limb::BITS as usize;

            let size = self.abs_size() as u32;
            // Extend for the extra limbs, then another one for any potential extra limbs
            self.ensure_capacity(extra_limbs + size + 1);

            unsafe {
                let ptr = self.limbs_uninit();
                let shift = ptr.offset(extra_limbs as isize);
                ll::copy_decr(ptr.as_const(), shift, self.abs_size());
                ll::zero(ptr, extra_limbs as i32);
            }

            self.size += (extra_limbs as i32) * self.sign();
        }

        debug_assert!(cnt < Limb::BITS as usize);

        if cnt == 0 { return; }

        let size = self.abs_size();

        unsafe {
            let ptr = self.limbs_mut();
            let c = ll::shl(ptr, ptr.as_const(), size, cnt as u32);
            if c > 0 {
                self.push(c);
            }
        }
    }
}

impl<'a> Shl<usize> for &'a Int {
    type Output = Int;

    #[inline]
    fn shl(self, cnt: usize) -> Int {
        let mut new = self.clone();
        new <<= cnt;
        new
    }
}

impl Shl<usize> for Int {
    type Output = Int;

    #[inline]
    fn shl(mut self, other: usize) -> Int {
        self <<= other;
        self
    }
}

impl ShrAssign<usize> for Int {
    #[inline]
    fn shr_assign(&mut self, mut cnt: usize) {
        debug_assert!(self.well_formed());
        if self.sign() == 0 { return; }

        if cnt >= Limb::BITS as usize {
            let removed_limbs = (cnt / Limb::BITS as usize) as u32;
            let size = self.abs_size();
            if removed_limbs as i32 >= size {
                *self = Int::zero();
                return;
            }
            debug_assert!(removed_limbs > 0);
            cnt = cnt % Limb::BITS as usize;

            unsafe {
                let ptr = self.limbs_mut();
                let shift = ptr.offset(removed_limbs as isize);
                let new_size = size - removed_limbs as i32;

                // Shift down a whole number of limbs
                ll::copy_incr(shift.as_const(), ptr, new_size);
                // Zero out the high limbs
                ll::zero(ptr.offset(new_size as isize),
                         removed_limbs as i32);

                self.size = new_size * self.sign();
            }
        }

        debug_assert!(cnt < Limb::BITS as usize);
        if cnt == 0 { return; }

        let size = self.abs_size();

        unsafe {
            let ptr = self.limbs_mut();
            ll::shr(ptr, ptr.as_const(), size, cnt as u32);
            self.normalize();
        }
    }
}

impl<'a> Shr<usize> for &'a Int {
    type Output = Int;

    #[inline]
    fn shr(self, other: usize) -> Int {
        let mut new = self.clone();
        new >>= other;
        new
    }
}

impl Shr<usize> for Int {
    type Output = Int;

    #[inline]
    fn shr(mut self, other: usize) -> Int {
        self >>= other;
        self
    }
}

#[derive(Copy, Clone)]
enum BitOp { And, Or, Xor }

fn bitop_ref(this: &mut Int, other: &Int, op: BitOp) -> Result<(), ()> {
    let this_sign = this.sign();
    let other_sign = other.sign();

    // if other is small, we can fall back to something that'll be
    // more efficient (especially if other is negative)
    if other.abs_size() <= 1 {
        // the magnitude of the limb
        let mut limb = other.to_single_limb();
        if other_sign < 0 {
            if limb.high_bit_set() {
                // the limb is too large to be put into two's
                // complement form (NB. that if other is positive, we
                // don't need to worry about two's complement, since
                // bitop_limb can handle unsigned Limbs)
                return Err(())
            } else {
                limb = -limb;
            }
        }

        // as mentioned above, we only have to say that `limb` is
        // signed when it is actually negative
        bitop_limb(this, limb, other_sign < 0, op);
        return Ok(());
    }

    if this_sign < 0 || other_sign < 0 {
        return Err(())
    }

    unsafe {
        let other_ptr = other.limbs();
        let min_size = std::cmp::min(this.abs_size(), other.abs_size());
        let max_size = std::cmp::max(this.abs_size(), other.abs_size());
        match op {
            BitOp::And => {
                let this_ptr = this.limbs_mut();
                ll::and_n(this_ptr, this_ptr.as_const(), other_ptr, min_size);
                this.size = min_size;
            }
            BitOp::Or => {
                this.ensure_capacity(max_size as u32);
                let this_ptr = this.limbs_uninit();
                ll::or_n(this_ptr, this_ptr.as_const(), other_ptr, min_size);
                if this.abs_size() < max_size {
                    ll::copy_rest(other_ptr, this_ptr, max_size, min_size);
                }
                this.size = max_size;
            }
            BitOp::Xor => {
                this.ensure_capacity(max_size as u32);
                let this_ptr = this.limbs_uninit();
                ll::xor_n(this_ptr, this_ptr.as_const(), other_ptr, min_size);
                if this.abs_size() < max_size {
                    ll::copy_rest(other_ptr, this_ptr, max_size, min_size);
                }
                this.size = max_size;
            }
        }
    }
    this.normalize();
    Ok(())
}

// one of the inputs is negative. The answer is as if `Int` was stored
// in two's complement (in infinite precision), which means converting
// to that format, doing the operation, and then converting back out
// of it, if necessary.
fn bitop_neg(mut a: Int, mut b: Int, op: BitOp) -> Int {
    debug_assert!(a.sign() < 0 || b.sign() < 0);
    let a_sign = a.sign();
    let b_sign = b.sign();

    if a_sign < 0 {
        a.negate_twos_complement();
    }
    if b_sign < 0 {
        b.negate_twos_complement();
    }
    let (mut a, b, a_sign, b_sign) = if a.abs_size() < b.abs_size() {
        (b, a, b_sign, a_sign)
    } else {
        (a, b, a_sign, b_sign)
    };

    unsafe {
        let a_ptr = a.limbs_mut();
        let b_ptr = b.limbs();
        let min_size = b.abs_size();
        let max_size = a.abs_size();

        let (neg_result, use_max_size) = match op {
            BitOp::And => {
                ll::and_n(a_ptr, a_ptr.as_const(), b_ptr, min_size);

                (a_sign < 0 && b_sign < 0,
                 b_sign < 0)
            }
            BitOp::Or => {
                ll::or_n(a_ptr, a_ptr.as_const(), b_ptr, min_size);
                // (no need to copy trailing, a is longer than b)

                (a_sign < 0 || b_sign < 0,
                 b_sign >= 0)
            }
            BitOp::Xor => {
                ll::xor_n(a_ptr, a_ptr.as_const(), b_ptr, min_size);
                if b_sign < 0 {
                    let ptr = a_ptr.offset(min_size as isize);
                    ll::not(ptr, ptr.as_const(), max_size - min_size);
                }
                ((a_sign < 0) ^ (b_sign < 0),
                 true)
            }
        };

        a.size = if use_max_size {
            max_size
        } else {
            min_size
        };
        if neg_result {
            a.negate_twos_complement();
        }
    }
    a.normalize();
    return a;
}

// do a bit operation on `a` and `b`.
//
// If `signed` only indicates whether to interpret `b` as two's
// complement or not (i.e. if it is true, then `1` is still `1`, and
// `-1` is `!0`)
fn bitop_limb(a: &mut Int, b: Limb, signed: bool, op: BitOp) {
    let a_sign = a.sign();
    let b_negative = signed && b.high_bit_set();
    let b_sign = if b_negative { -1 } else if b == 0 { 0 } else { 1 };

    if a_sign < 0 {
        a.negate_twos_complement();
    }
    // b is already in two's complement if it is negative

    if a_sign == 0 {
        match op {
            // 0 ^ x == 0 | x == x
            BitOp::Or | BitOp::Xor => {
                if b_sign < 0 {
                    a.push(-b);
                    a.negate();
                } else {
                    a.push(b)
                }
            }
            // 0 & x == 0
            BitOp::And => {}
        }
    } else {
        unsafe {
            let mut a_ptr = a.limbs_mut();
            let min_size = if b == 0 { 0 } else { 1 };
            let max_size = a.abs_size();
            // we've got to have space to write data to this pointer
            debug_assert!(max_size >= 1);

            let (neg_result, use_max_size) = match op {
                BitOp::And => {
                    *a_ptr = *a_ptr & b;
                    (a_sign < 0 && b_sign < 0,
                     b_sign < 0)
                }
                BitOp::Or => {
                    *a_ptr = *a_ptr | b;
                    (a_sign < 0 || b_sign < 0,
                     b_sign >= 0)
                }
                BitOp::Xor => {
                    *a_ptr = *a_ptr ^ b;
                    if b_sign < 0 {
                        let ptr = a_ptr.offset(min_size as isize);
                        ll::not(ptr, ptr.as_const(), max_size - min_size);
                    }
                    ((a_sign < 0) ^ (b_sign < 0),
                     true)
                }
            };
            a.size = if use_max_size {
                max_size
            } else {
                min_size
            };
            if neg_result {
                a.negate_twos_complement();
            }
        }
    }
    a.normalize();
}

impl<'a> BitAnd<Limb> for Int {
    type Output = Int;

    fn bitand(mut self, other: Limb) -> Int {
        self &= other;
        self
    }
}

impl BitAndAssign<Limb> for Int {
    fn bitand_assign(&mut self, other: Limb) {
        bitop_limb(self, other, false, BitOp::And)
    }
}

impl<'a> BitAnd<&'a Int> for Int {
    type Output = Int;

    fn bitand(mut self, other: &'a Int) -> Int {
        if let Ok(_) = bitop_ref(&mut self, other, BitOp::And) {
            self
        } else {
            bitop_neg(self, other.clone(), BitOp::And)
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

    fn bitand(mut self, other: Int) -> Int {
        if let Ok(_) = bitop_ref(&mut self, &other, BitOp::And) {
            self
        } else {
            bitop_neg(self, other, BitOp::And)
        }
    }
}

impl BitAndAssign<Int> for Int {
    #[inline]
    fn bitand_assign(&mut self, other: Int) {
        if let Err(_) = bitop_ref(self, &other, BitOp::And) {
            let res = &*self & other;
            *self = res;
        }
    }
}
impl<'a> BitAndAssign<&'a Int> for Int {
    #[inline]
    fn bitand_assign(&mut self, other: &'a Int) {
        if let Err(_) = bitop_ref(self, other, BitOp::And) {
            let res = &*self & other;
            *self = res;
        }
    }
}

impl BitOr<Limb> for Int {
    type Output = Int;

    fn bitor(mut self, other: Limb) -> Int {
        self |= other;
        self
    }
}

impl BitOrAssign<Limb> for Int {
    fn bitor_assign(&mut self, other: Limb) {
        bitop_limb(self, other, false, BitOp::Or)
    }
}

impl<'a> BitOr<&'a Int> for Int {
    type Output = Int;

    fn bitor(mut self, other: &'a Int) -> Int {
        if let Ok(_) = bitop_ref(&mut self, other, BitOp::Or) {
            self
        } else {
            bitop_neg(self, other.clone(), BitOp::Or)
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
    fn bitor(mut self, other: Int) -> Int {
        if let Ok(_) = bitop_ref(&mut self, &other, BitOp::Or) {
            self
        } else {
            bitop_neg(self, other, BitOp::Or)
        }
    }
}

impl BitOrAssign<Int> for Int {
    #[inline]
    fn bitor_assign(&mut self, other: Int) {
        if let Err(_) = bitop_ref(self, &other, BitOp::Or) {
            let res = &*self | other;
            *self = res;
        }
    }
}
impl<'a> BitOrAssign<&'a Int> for Int {
    #[inline]
    fn bitor_assign(&mut self, other: &'a Int) {
        if let Err(_) = bitop_ref(self, &other, BitOp::Or) {
            let res = &*self | other;
            *self = res;
        }
    }
}

impl<'a> BitXor<Limb> for Int {
    type Output = Int;

    fn bitxor(mut self, other: Limb) -> Int {
        self ^= other;
        self
    }
}

impl BitXorAssign<Limb> for Int {
    fn bitxor_assign(&mut self, other: Limb) {
        bitop_limb(self, other, false, BitOp::Xor)
    }
}

impl<'a> BitXor<&'a Int> for Int {
    type Output = Int;

    fn bitxor(mut self, other: &'a Int) -> Int {
        if let Ok(_) = bitop_ref(&mut self, other, BitOp::Xor) {
            self
        } else {
            bitop_neg(self, other.clone(), BitOp::Xor)
        }
    }
}

impl<'a> BitXor<Int> for &'a Int {
    type Output = Int;

    #[inline]
    fn bitxor(self, other: Int) -> Int {
        other.bitxor(self)
    }
}

impl<'a, 'b> BitXor<&'a Int> for &'b Int {
    type Output = Int;

    #[inline]
    fn bitxor(self, other: &'a Int) -> Int {
        self.clone().bitxor(other)
    }
}

impl BitXor<Int> for Int {
    type Output = Int;

    #[inline]
    fn bitxor(mut self, other: Int) -> Int {
        if let Ok(_) = bitop_ref(&mut self, &other, BitOp::Xor) {
            self
        } else {
            bitop_neg(self, other, BitOp::Xor)
        }
    }
}

impl BitXorAssign<Int> for Int {
    #[inline]
    fn bitxor_assign(&mut self, other: Int) {
        if let Err(_) = bitop_ref(self, &other, BitOp::Xor) {
            let res = &*self ^ other;
            *self = res;
        }
    }
}
impl<'a> BitXorAssign<&'a Int> for Int {
    #[inline]
    fn bitxor_assign(&mut self, other: &'a Int) {
        if let Err(_) = bitop_ref(self, &other, BitOp::Xor) {
            let res = &*self ^ other;
            *self = res;
        }
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

        impl AddAssign<$t> for Int {
            #[inline]
            fn add_assign(&mut self, other: $t) {
                if other < 0 {
                    *self -= Limb(other.abs() as BaseInt);
                } else if other > 0 {
                    *self += Limb(other as BaseInt);
                }
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

        impl SubAssign<$t> for Int {
            #[inline]
            fn sub_assign(&mut self, other: $t) {
                if other < 0 {
                    *self += Limb(other.abs() as BaseInt);
                } else if other > 0 {
                    *self -= Limb(other as BaseInt);
                }
            }
        }

        impl Mul<$t> for Int {
            type Output = Int;

            #[inline]
            fn mul(mut self, other: $t) -> Int {
                self *= other;
                self
            }
        }

        impl MulAssign<$t> for Int {
            #[inline]
            fn mul_assign(&mut self, other: $t) {
                if other == 0 {
                    self.size = 0;
                } else if other == -1 {
                    self.negate();
                } else if other < 0 {
                    self.negate();
                    *self *= Limb(other.abs() as BaseInt);
                } else {
                    *self *= Limb(other as BaseInt);
                }
            }
        }

        impl DivAssign<$t> for Int {
            #[inline]
            fn div_assign(&mut self, other: $t) {
                if other == 0 {
                    ll::divide_by_zero();
                }
                if other == 1 || self.sign() == 0 {
                    return;
                }
                if other == -1 {
                    self.negate();
                } else if other < 0 {
                    self.negate();
                    *self /= Limb(other.abs() as BaseInt);
                } else {
                    *self /= Limb(other as BaseInt);
                }
            }
        }

        impl Div<$t> for Int {
            type Output = Int;

            #[inline]
            fn div(mut self, other: $t) -> Int {
                self /= other;
                self
            }
        }

        impl RemAssign<$t> for Int {
            #[inline]
            fn rem_assign(&mut self, other: $t) {
                let res = &*self % other;
                *self = res;
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

                return self % Limb(other.abs() as BaseInt);
            }
        }

        impl DivRem<$t> for Int {
            type Output = (Int, $t);

            #[inline]
            fn divrem(mut self, other: $t) -> Self::Output {
                if other == 0 {
                    ll::divide_by_zero();
                }
                let sign = self.sign();
                let (q, r) = {
                    if other == 1 || sign == 0 {
                        return (self, 0);
                    } else if other == -1 {
                        self.negate();
                        return (self, 0);
                    } else if other < 0 {
                        self.negate();
                        self.divrem(Limb(other.abs() as BaseInt))
                    } else {
                        self.divrem(Limb(other as BaseInt))
                    }
                };
                let r = (r.0 as $t).checked_mul(sign).unwrap();
                debug_assert!(sign > 0 || r <= 0);
                debug_assert!(sign < 0 || r >= 0);
                debug_assert!(r.abs() < other.abs());
                (q, r)
            }
        }

        impl BitAndAssign<$t> for Int {
            #[inline]
            fn bitand_assign(&mut self, other: $t) {
                bitop_limb(self, Limb(other as BaseInt), true, BitOp::And)
            }
        }

        impl BitOrAssign<$t> for Int {
            #[inline]
            fn bitor_assign(&mut self, other: $t) {
                bitop_limb(self, Limb(other as BaseInt), true, BitOp::Or)
            }
        }

        impl BitXorAssign<$t> for Int {
            #[inline]
            fn bitxor_assign(&mut self, other: $t) {
                bitop_limb(self, Limb(other as BaseInt), true, BitOp::Xor)
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

        impl AddAssign<$t> for Int {
            #[inline]
            fn add_assign(&mut self, other: $t) {
                if other != 0 {
                    *self += Limb(other as BaseInt);
                }
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

        impl SubAssign<$t> for Int {
            #[inline]
            fn sub_assign(&mut self, other: $t) {
                if other != 0 {
                    *self -= Limb(other as BaseInt);
                }
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

        impl MulAssign<$t> for Int {
            #[inline]
            fn mul_assign(&mut self, other: $t) {
                if other == 0 {
                    self.size = 0;
                } else if other > 1 && self.sign() != 0 {
                    *self *= Limb(other as BaseInt);
                }
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

        impl DivAssign<$t> for Int {
            #[inline]
            fn div_assign(&mut self, other: $t) {
                if other == 0 {
                    ll::divide_by_zero();
                } else if other > 1 && self.sign() != 0 {
                    *self /= Limb(other as BaseInt);
                }
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

                return self % Limb(other as BaseInt);
            }
        }
        impl RemAssign<$t> for Int {
            #[inline]
            fn rem_assign(&mut self, other: $t) {
                *self %= Limb(other as BaseInt);
            }
        }

        impl DivRem<$t> for Int {
            type Output = (Int, $t);

            #[inline]
            fn divrem(self, other: $t) -> Self::Output {
                let other = other as BaseInt;
                let (q, r) = self.divrem(Limb(other));
                debug_assert!(r < other);
                (q, r.0 as $t)
            }
        }

        impl BitAndAssign<$t> for Int {
            #[inline]
            fn bitand_assign(&mut self, other: $t) {
                bitop_limb(self, Limb(other as BaseInt), false, BitOp::And)
            }
        }

        impl BitOrAssign<$t> for Int {
            #[inline]
            fn bitor_assign(&mut self, other: $t) {
                bitop_limb(self, Limb(other as BaseInt), false, BitOp::Or)
            }
        }

        impl BitXorAssign<$t> for Int {
            #[inline]
            fn bitxor_assign(&mut self, other: $t) {
                bitop_limb(self, Limb(other as BaseInt), false, BitOp::Xor)
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

        impl BitAnd<$t> for Int {
            type Output = Int;

            #[inline]
            fn bitand(mut self, other: $t) -> Int {
                self &= other;
                self
            }
        }

        impl<'a> BitAnd<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn bitand(self, other: $t) -> Int {
                self.clone() & other
            }
        }

        impl BitAnd<Int> for $t {
            type Output = Int;

            #[inline]
            fn bitand(self, other: Int) -> Int {
                other & self
            }
        }

        impl<'a> BitAnd<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn bitand(self, other: &'a Int) -> Int {
                other & self
            }
        }

        impl BitOr<$t> for Int {
            type Output = Int;

            #[inline]
            fn bitor(mut self, other: $t) -> Int {
                self |= other;
                self
            }
        }

        impl<'a> BitOr<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn bitor(self, other: $t) -> Int {
                self.clone() | other
            }
        }

        impl BitOr<Int> for $t {
            type Output = Int;

            #[inline]
            fn bitor(self, other: Int) -> Int {
                other | self
            }
        }

        impl<'a> BitOr<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn bitor(self, other: &'a Int) -> Int {
                other | self
            }
        }

        impl BitXor<$t> for Int {
            type Output = Int;

            #[inline]
            fn bitxor(mut self, other: $t) -> Int {
                self ^= other;
                self
            }
        }

        impl<'a> BitXor<$t> for &'a Int {
            type Output = Int;

            #[inline]
            fn bitxor(self, other: $t) -> Int {
                self.clone() ^ other
            }
        }

        impl BitXor<Int> for $t {
            type Output = Int;

            #[inline]
            fn bitxor(self, other: Int) -> Int {
                other ^ self
            }
        }

        impl<'a> BitXor<&'a Int> for $t {
            type Output = Int;

            #[inline]
            fn bitxor(self, other: &'a Int) -> Int {
                other ^ self
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
            return *self.limbs() == (other.abs() as BaseInt);
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


const MAX_LIMB: u64 = !0 >> (64 - Limb::BITS);

// do a sign-magnitude comparison
fn eq_64(x: &Int, mag: u64, neg: bool) -> bool {
    let sign = if mag == 0 { 0 } else if neg { -1 } else { 1 };
    if x.sign() != sign {
        return false
    } else if mag == 0 {
        // we're guaranteed to have x == 0 since the signs match
        return true
    }


    let abs_size = x.abs_size();
    debug_assert!(abs_size >= 1);
    let ptr = x.limbs();
    let lo_limb = *ptr;

    if mag < MAX_LIMB {
        abs_size == 1 && lo_limb.0 == mag as BaseInt
    } else {
        // we can only get here when Limbs are small, and the Int
        // is large
        assert_eq!(Limb::BITS, 32);

        if abs_size == 2 {
            let hi_limb = unsafe {*ptr.offset(1)};
            hi_limb.0 == (mag >> 32) as BaseInt
                && lo_limb.0 == mag as BaseInt
        } else {
            false
        }
    }
}

fn cmp_64(x: &Int, mag: u64, neg: bool) -> Ordering {
    if mag == 0 {
        return x.sign().cmp(&0)
    }

    let size = x.size;
    if (size < 0) != neg || size == 0 {
        // they have different signs
        return size.cmp(&if neg {-1} else {1})
    }
    let ptr = x.limbs();
    let lo_limb = *ptr;

    let mag_ord = if mag < MAX_LIMB {
        (size.abs(), lo_limb.0).cmp(&(1, mag as BaseInt))
    } else {
        assert_eq!(Limb::BITS, 32);
        debug_assert!(size.abs() >= 1);
        let hi_limb = if size.abs() == 1 {
            Limb(0)
        } else {
            unsafe {*ptr.offset(1)}
        };

        (size.abs(), hi_limb.0, lo_limb.0)
            .cmp(&(2, (mag >> 32) as BaseInt, mag as BaseInt))
    };
    if size < 0 && neg {
        // both negative, so the magnitude orderings need to be
        // flipped
        mag_ord.reverse()
    } else {
        mag_ord
    }
}

impl PartialEq<u64> for Int {
    fn eq(&self, &other: &u64) -> bool {
        eq_64(self, other, false)
    }
}

impl PartialEq<Int> for u64 {
    fn eq(&self, other: &Int) -> bool {
        eq_64(other, *self, false)
    }
}

impl PartialOrd<u64> for Int {
    fn partial_cmp(&self, &other: &u64) -> Option<Ordering> {
        Some(cmp_64(self, other, false))
    }
}

impl PartialOrd<Int> for u64 {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(cmp_64(other, *self, false).reverse())
    }
}

impl PartialEq<i64> for Int {
    fn eq(&self, &other: &i64) -> bool {
        eq_64(self, other.abs() as u64, other < 0)
    }
}

impl PartialEq<Int> for i64 {
    fn eq(&self, other: &Int) -> bool {
        eq_64(other, self.abs() as u64, *self < 0)
    }
}

impl PartialOrd<i64> for Int {
    fn partial_cmp(&self, &other: &i64) -> Option<Ordering> {
        Some(cmp_64(self, other.abs() as u64, other < 0))
    }
}

impl PartialOrd<Int> for i64 {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(cmp_64(other, self.abs() as u64, *self < 0).reverse())
    }
}

macro_rules! impl_from_prim (
    (signed $($t:ty),*) => {
        $(impl ::std::convert::From<$t> for Int {
            #[allow(exceeding_bitshifts)] // False positives for the larger-than BaseInt case
            fn from(val: $t) -> Int {
                if val == 0 {
                    return Int::zero();
                } if val == <$t>::min_value() {
                    let shift = val.trailing_zeros() as usize;
                    let mut i = Int::one();
                    i = i << shift;
                    return -i;
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
                if ::std::mem::size_of::<BaseInt>() < ::std::mem::size_of::<$t>() {
                    // Handle conversion where BaseInt = u32 and $t = i64
                    if i.abs_size() >= 2 { // Fallthrough if there's only one limb
                        let lower = i.to_single_limb().0 as $t;
                        let higher = unsafe { (*i.ptr.offset(1)).0 } as $t;

                        // Combine the two
                        let n : $t = lower | (higher << Limb::BITS);

                        // Apply the sign
                        return n.wrapping_mul(sign);
                    }
                }
                let n = i.to_single_limb().0;
                // Using wrapping_mul to account for when the binary
                // representation of n == $t::MIN
                return (n as $t).wrapping_mul(sign);
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
                        let n : $t = lower | (higher << Limb::BITS);

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
            ptr: unsafe { Unique::new(alloc::heap::EMPTY as *mut Limb) },
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

    fn steps_between_by_one(start: &Self, end: &Self) -> Option<usize> {
        Self::steps_between(start, end, &Self::one())
    }

    fn is_negative(&self) -> bool {
        self.sign() < 0
    }

    fn replace_one(&mut self) -> Self {
        mem::replace(self, Self::one())
    }

    fn replace_zero(&mut self) -> Self {
        mem::replace(self, Self::zero())
    }

    fn add_one(&self) -> Self {
        self + 1
    }

    fn sub_one(&self) -> Self {
        self - 1
    }
}

/// Trait for generating random `Int`.
///
/// # Example
///
/// Generate a random `Int` of size `256` bits:
///
/// ```
/// extern crate rand;
/// extern crate ramp;
///
/// use ramp::RandomInt;
///
/// fn main() {
///     let mut rng = rand::thread_rng();
///     let big_i = rng.gen_int(256);
/// }
/// ```
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
        assert!(bits > 0);

        let limbs = (bits / &Limb::BITS) as u32;
        let rem = bits % &Limb::BITS;

        let mut i = Int::with_capacity(limbs + 1);

        for _ in 0..limbs {
            let limb = Limb(self.gen());
            i.push(limb);
        }

        if rem > 0 {
            let final_limb = Limb(self.gen());
            i.push(final_limb >> (&Limb::BITS - rem));
        }

        i.normalize();

        i
    }

    fn gen_int(&mut self, bits: usize) -> Int {
        let i = self.gen_uint(bits);

        let r = if i == Int::zero() {
            // ...except that if the BigUint is zero, we need to try
            // again with probability 0.5. This is because otherwise,
            // the probability of generating a zero BigInt would be
            // double that of any other number.
            if self.gen() {
                return self.gen_uint(bits);
            } else {
                i
            }
        } else if self.gen() {
            -i
        } else {
            i
        };

        r
    }

    fn gen_uint_below(&mut self, bound: &Int) -> Int {
        assert!(*bound > Int::zero());
        // If we haven't got a valid number after 10,000 tries, then something
        // has probably gone wrong, as there is a 1 in 10^3000 chance of this
        // happening, in the worst case.
        const ITER_LIMIT : usize = 10000;

        let bits = bound.bit_length() as usize;

        // Since it uses a number of bits, gen_uint may return a number too large,
        // loop until we generate a valid number.
        // Since the greatest gap between the bound and the largest number produced
        // is when bound = 2^n (bit string [100000....]), we have, at worst, a 50/50
        // chance of producing an invalid number each iteration.
        let mut count = 0;
        while count < ITER_LIMIT {
            let n = self.gen_uint(bits);
            if n < *bound { return n; }
            count += 1;
        }

        panic!("No valid number generated in {} iterations.\n\
                Please open an issue at https://github.com/Aatch/ramp", ITER_LIMIT);
    }

    fn gen_int_range(&mut self, lbound: &Int, ubound: &Int) -> Int {
        assert!(*lbound < *ubound);
        lbound + self.gen_uint_below(&(ubound - lbound))
    }
}

#[cfg(test)]
mod test {
    use std;
    use std::hash::{Hash, Hasher};
    use rand::{self, Rng};
    use test::{self, Bencher};
    use super::*;
    use ll::limb::Limb;
    use traits::DivRem;
    use std::str::FromStr;
    use std::num::Zero;

    macro_rules! assert_mp_eq (
        ($l:expr, $r:expr) => (
            {
                let l : &Int = &$l;
                let r : &Int = &$r;
                if l != r {
                    println!("assertion failed: {} == {}", stringify!($l), stringify!($r));
                    panic!("{:} != {:}", l, r);
                }
            }
        )
    );

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
    fn num_base_digits_pow2() {
        use ::ll::base::num_base_digits;
        let cases = [
            ("10", 2, 4), // 0b 1010
            ("15", 2, 4), // 0b 1111
            ("16", 2, 5), // 0b10000
            ("1023", 2, 10), // 0b 1111111111
            ("1024", 2, 11), // 0b10000000000
            ("341", 4, 5), // 4»11111
            ("5461", 4, 7), // 4»1111111
            ("16383", 4, 7), // 4» 3333333
            ("16384", 4, 8), // 4»10000000
            ("65535", 4, 8), // 4»33333333
            ("299593", 8, 7), // 8»1111111 // 8**0 + 8**1 + 8**2 + 8**3 + 8**4 + 8**5 + 8**6
            ("299594", 8, 7), // 8»1111112
            ("2097151", 8, 7), // 8» 7777777
            ("2097152", 8, 8), // 8»10000000
            ("268435455", 16, 7), // 0x fffffff
            ("268435456", 16, 8), // 0x10000000
            ("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095", 2, 512), // 512 bits with value 1 -> 1 Limb
            ("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096", 2, 513), // 513 bits -> 2 Limbs
        ];
        for &(s, base, digits) in cases.iter() {
            let i : Int = s.parse().unwrap();
            unsafe {
                assert_eq!(digits,
                           num_base_digits(i.limbs(), i.abs_size(), base));
            }
        }
    }

    #[test]
    fn num_base_digits() {
        use ::ll::base::num_base_digits;
        let cases = [
            ("0", 15, 1),
            ("0", 58, 1),
            ("49172", 10, 5),
            ("49172", 57, 3), // [15, 7, 38], 38 + 7*57 + 15*57**2 = 49172
            ("185192", 57, 3), // [56, 56, 56], 56 + 56*57 + 56*57**2 = 185192
            ("185193", 57, 4), // [1, 0, 0, 0], 1*57**3 = 185193
            ("250046", 63, 3), // [62, 62, 62], 62 + 62*63 + 62*63**2 = 250046
            ("250047", 63, 4), // [1, 0, 0, 0], 1*63**3 = 250047
            ("274624", 65, 3), // [64, 64, 64], 64 + 64*65 + 64*65**2 = 274624
            ("274625", 65, 4), // [1, 0, 0, 0], 1*65**3 = 274625
        ];
        for &(s, base, digits) in cases.iter() {
            let i : Int = s.parse().unwrap();
            unsafe {
                let estimate = num_base_digits(i.limbs(), i.abs_size(), base);
                assert!(digits == estimate || digits == estimate - 1);
            }
        }
    }

    #[test]
    fn pow() {
        let bases = ["0", "1", "190000000000000", "192834857324591531",
                     "340282366920938463463374607431768211456", // 2**128
                     "100000000", "-1", "-100", "-200", "-192834857324591531",
                     "-431343873217510631841",
                     "-340282366920938463463374607431768211456"];

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
            // (2**64 - 1) * 2**64 + 2**64 == 2**128
            ("340282366920938463444927863358058659840", "18446744073709551616",
             "340282366920938463463374607431768211456"),
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
            ("237", "236", "1"),
            ("-192834857324591531", "-431343873217510631841", "431151038360186040310"),
            // (2**64 - 1) * 2**64 - -2**64 == 2**128
            ("340282366920938463444927863358058659840", "-18446744073709551616",
             "340282366920938463463374607431768211456"),
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
    #[should_panic(expected = "divide by zero")]
    #[cfg(debug_assertions)] // only a panic in this mode
    fn divmod_zero() {
        Int::from(1).divmod(&Int::zero());
    }

    #[test]
    fn rem() {
        let cases = [
            ("2", "1", "0"),
            ("1", "2", "1"),
            ("100", "2", "0"),
            ("100", "3", "1"),
            ("234129835798275032157029375235", "4382109473241242142341234", "2490861941946976021925083")
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = &l % &r;
            assert_mp_eq!(val, a);
        }
    }

    #[test]
    fn divrem() {
        let cases = [
            ("20000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000001",
             "100000000000000000000000000000000000000000000001",
             "200000000000000000000000000000000000000000000001",
             "100000000000000000000000000000000000000000000000"),
        ];

        for t in cases.into_iter() {
            let dividend: Int = t.0.parse().unwrap();
            let divisor: Int = t.1.parse().unwrap();
            let expected_quotient: Int = t.2.parse().unwrap();
            let expected_remainder: Int = t.3.parse().unwrap();

            let (actual_quotient, actual_remainder) = (&dividend).divrem(&divisor);
            assert_mp_eq!(actual_quotient, expected_quotient);
            assert_mp_eq!(actual_remainder, expected_remainder);
        }
    }

    #[test]
    fn sqrt_rem() {
        let cases = [
            ("0", "0", "0"),
            ("1", "1", "0"),
            ("2", "1", "1"),
            ("3", "1", "2"),
            ("4", "2", "0"),
            ("1000", "31", "39"),
            ("15241578753238836750495351562536198787501905199875019052100",
             "123456789012345678901234567890", "0"),
            ("15241578753238836750495351562536198787501905199875019052099",
             "123456789012345678901234567889", "246913578024691357802469135778"),
            ("15241578753238836750495351562536198787501905199875019052101",
             "123456789012345678901234567890", "1"),
                ];

        for &(x, sqrt, rem) in &cases {
            let x : Int = x.parse().unwrap();
            let sqrt : Int = sqrt.parse().unwrap();
            let rem : Int = rem.parse().unwrap();

            if x != 0 {
                assert!((-&x).sqrt_rem().is_none());
            }

            let (s, r) = x.sqrt_rem().unwrap();
            assert_mp_eq!(s, sqrt);
            assert_mp_eq!(r, rem);

        }
    }

    #[test]
    fn bitand() {
        let cases = [
            ("0", "1", "0"),
            ("17", "65", "1"),
            ("-17", "65", "65"),
            ("17", "-65", "17"),
            ("-17", "-65", "-81"),
            ("0", "543253451643657932075830214751263521", "0"),
            ("-1", "543253451643657932075830214751263521", "543253451643657932075830214751263521"),
            ("47398217493274092174042109472", "9843271092740214732017421", "152974816756326460458496"),
            ("87641324986400000000000", "31470973247490321000000000000000", "2398658832415825854464"),
            ("-87641324986400000000000", "31470973247490321000000000000000", "31470973245091662167584174145536"),
            ("87641324986400000000000", "-31470973247490321000000000000000", "85242666153984174129152"),
            ("-87641324986400000000000", "-31470973247490321000000000000000", "-31470973332732987153984174129152"),
        ];

        for &(l_, r_, a) in cases.iter() {
            let l : Int = l_.parse().unwrap();
            let r : Int = r_.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = &l & &r;
            assert_mp_eq!(val, a);

            if l.bit_length() <= 31 {
                let l: i32 = l_.parse().unwrap();
                let val = l & &r;
                assert_mp_eq!(val, a);
            }
            if r.bit_length() <= 31 {
                let r: i32 = r_.parse().unwrap();
                let val = &l & r;
                assert_mp_eq!(val, a);
            }
        }
    }

    #[test]
    fn bitor() {
        let cases = [
            ("0", "1", "1"),
            ("17", "65", "81"),
            ("-17", "65", "-17"),
            ("17", "-65", "-65"),
            ("-17", "-65", "-1"),
            ("0", "543253451643657932075830214751263521", "543253451643657932075830214751263521"),
            ("-1", "543253451643657932075830214751263521", "-1"),
            ("47398217493274092174042109472", "9843271092740214732017421","47407907789550076062313668397"),
            ("87641324986400000000000", "31470973247490321000000000000000", "31470973332732987153984174145536"),
            ("-87641324986400000000000", "31470973247490321000000000000000", "-85242666153984174145536"),
            ("87641324986400000000000", "-31470973247490321000000000000000", "-31470973245091662167584174129152"),
            ("-87641324986400000000000", "-31470973247490321000000000000000", "-2398658832415825870848"),
        ];

        for &(l_, r_, a) in cases.iter() {
            let l : Int = l_.parse().unwrap();
            let r : Int = r_.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = &l | &r;
            assert_mp_eq!(val, a);

            if l.bit_length() <= 31 {
                let l: i32 = l_.parse().unwrap();
                let val = l | &r;
                assert_mp_eq!(val, a);
            }
            if r.bit_length() <= 31 {
                let r: i32 = r_.parse().unwrap();
                let val = &l | r;
                assert_mp_eq!(val, a);
            }
        }
    }

    #[test]
    fn bitxor() {
        let cases = [
            ("0", "1", "1"),
            ("17", "65", "80"),
            ("-17", "65", "-82"),
            ("17", "-65", "-82"),
            ("-17", "-65", "80"),
            ("0", "543253451643657932075830214751263521", "543253451643657932075830214751263521"),
            ("-1", "543253451643657932075830214751263521", "-543253451643657932075830214751263522"),
            ("47398217493274092174042109472", "9843271092740214732017421","47407754814733319735853209901"),
            ("87641324986400000000000", "31470973247490321000000000000000", "31470973330334328321568348291072"),
            ("-87641324986400000000000", "31470973247490321000000000000000", "-31470973330334328321568348291072"),
            ("87641324986400000000000", "-31470973247490321000000000000000", "-31470973330334328321568348258304"),
            ("-87641324986400000000000", "-31470973247490321000000000000000", "31470973330334328321568348258304"),
        ];

        for &(l_, r_, a) in cases.iter() {
            let l : Int = l_.parse().unwrap();
            let r : Int = r_.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = &l ^ &r;
            assert_mp_eq!(val, a);

            if l.bit_length() <= 31 {
                let l: i32 = l_.parse().unwrap();
                let val = l ^ &r;
                assert_mp_eq!(val, a);
            }
            if r.bit_length() <= 31 {
                let r: i32 = r_.parse().unwrap();
                let val = &l ^ r;
                assert_mp_eq!(val, a);
            }
        }
    }

    #[test]
    fn is_even() {
        let cases = [
            ("0", true),
            ("1", false),
            ("47398217493274092174042109472", true),
            ("47398217493274092174042109471", false),
        ];

        for &(v, even) in cases.iter() {
            let val : Int = v.parse().unwrap();

            assert_eq!(val.is_even(), even);

            let val = -val;
            assert_eq!(val.is_even(), even);
        }

    }

    #[test]
    fn trailing_zeros() {
        let cases = [
            ("0", 0),
            ("1", 0),
            ("16", 4),
            ("3036937844145311324764506857395738547330878864826266812416", 100)
        ];

        for &(v, count) in cases.iter() {
            let val : Int = v.parse().unwrap();

            assert_eq!(val.trailing_zeros(), count);
        }

    }

    #[test]
    fn arith_prim() {
        // Test that the Int/prim overloads are working as expected

        let x : Int = "100".parse().unwrap();

        // Int op prim
        assert_mp_eq!(&x + 1usize, "101".parse().unwrap());
        assert_mp_eq!(&x - 1usize, "99".parse().unwrap());

        assert_mp_eq!(&x + 1i32, "101".parse().unwrap());
        assert_mp_eq!(&x - 1i32, "99".parse().unwrap());

        assert_mp_eq!(&x + (-1i32), "99".parse().unwrap());
        assert_mp_eq!(&x - (-1i32), "101".parse().unwrap());
        assert_mp_eq!(&x + (-101i32), "-1".parse().unwrap());
        assert_mp_eq!(&x - 101i32, "-1".parse().unwrap());

        assert_mp_eq!(&x - 100usize, Int::zero());
        assert_mp_eq!(-&x + 100usize, Int::zero());
        assert_mp_eq!(&x - 100i32, Int::zero());
        assert_mp_eq!(&x + (-100i32), Int::zero());
        assert_mp_eq!(-&x + 100i32, Int::zero());
        assert_mp_eq!(-&x - (-100i32), Int::zero());

        assert_mp_eq!(&x * 2usize, "200".parse().unwrap());

        assert_mp_eq!(&x * 2i32, "200".parse().unwrap());
        assert_mp_eq!(&x * (-2i32), "-200".parse().unwrap());

        assert_mp_eq!(&x / 2usize, "50".parse().unwrap());
        assert_mp_eq!(&x / 2i32, "50".parse().unwrap());
        assert_mp_eq!(&x / (-2i32), "-50".parse().unwrap());

        assert_mp_eq!(&x % 2usize, "0".parse().unwrap());
        assert_mp_eq!(&x % 2i32, "0".parse().unwrap());
        assert_mp_eq!(&x % (-2i32), "0".parse().unwrap());

        let x : Int = "5".parse().unwrap();

        // prim op Int
        assert_mp_eq!(1usize + &x, "6".parse().unwrap());
        assert_mp_eq!(1usize - &x, "-4".parse().unwrap());

        assert_mp_eq!(1i32 + &x, "6".parse().unwrap());
        assert_mp_eq!(1i32 - &x, "-4".parse().unwrap());

        assert_mp_eq!((-1i32) + &x, "4".parse().unwrap());
        assert_mp_eq!((-1i32) - &x, "-6".parse().unwrap());

        assert_mp_eq!(2usize * &x, "10".parse().unwrap());

        assert_mp_eq!(2i32 * &x, "10".parse().unwrap());
        assert_mp_eq!((-2i32) * &x, "-10".parse().unwrap());

        assert_mp_eq!(20usize / &x, "4".parse().unwrap());
        assert_mp_eq!(20i32 / &x, "4".parse().unwrap());
        assert_mp_eq!((-20i32) / &x, "-4".parse().unwrap());
    }

    #[test]
    fn int_from() {
        let i = Int::from(::std::i64::MIN);
        assert_eq!(i64::from(&i), ::std::i64::MIN);

        let i = Int::from(::std::i32::MIN);
        assert_eq!(i32::from(&i), ::std::i32::MIN);

        let i = Int::from(::std::usize::MAX);
        assert_eq!(usize::from(&i), ::std::usize::MAX);
    }

    const RAND_ITER : usize = 1000;

    #[test]
    fn div_rand() {
        let mut rng = rand::thread_rng();
        for _ in 0..RAND_ITER {
            let x = rng.gen_int(640);
            let y = rng.gen_int(320);

            let (q, r) = x.divmod(&y);
            let val = (q * &y) + r;

            assert_mp_eq!(val, x);
        }
    }

    #[test]
    fn sqr_rand() {
        let mut rng = rand::thread_rng();
        for _ in 0..RAND_ITER {
            let x = rng.gen_int(640);

            let xs = x.square();
            let xm = &x * &x;

            assert_mp_eq!(xm, xs);
        }
    }


    #[test]
    fn shl_rand() {
        let mut rng = rand::thread_rng();
        for _ in 0..RAND_ITER {
            let x = rng.gen_int(640);

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
        for _ in 0..RAND_ITER {
            let pow : usize = rng.gen_range(64, 8196);
            let mul_by = Int::from(2).pow(pow);

            let x = rng.gen_int(640);

            let shift = &x << pow;
            let mul = x * mul_by;

            assert_mp_eq!(shift, mul);
        }
    }

    #[test]
    fn shr_rand() {
        let mut rng = rand::thread_rng();
        for _ in 0..RAND_ITER {
            let pow : usize = rng.gen_range(64, 8196);
            let x = rng.gen_int(640);

            let shift_up = &x << pow;
            let shift_down = shift_up >> pow;

            assert_mp_eq!(shift_down, x);
        }
    }

    #[test]
    fn bitand_rand() {
        let mut rng = rand::thread_rng();
        for _ in 0..RAND_ITER {
            let x = rng.gen_int(640);
            let y = rng.gen_int(640);

            let _ = x & y;
        }
    }

    #[test]
    fn hash_rand() {
        let mut rng = rand::thread_rng();
        for _ in 0..RAND_ITER {
            let x1 = rng.gen_int(640);
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

    #[test]
    #[should_panic]
    fn gen_uint_with_zero_bits() {
        let mut rng = rand::thread_rng();
        rng.gen_uint(0);
    }

    #[test]
    #[should_panic]
    fn gen_int_with_zero_bits() {
        let mut rng = rand::thread_rng();
        rng.gen_int(0);
    }

    #[test]
    #[should_panic]
    fn gen_uint_below_zero_or_negative() {
        let mut rng = rand::thread_rng();

        let i = Int::from(0);
        rng.gen_uint_below(&i);

        let j = Int::from(-1);
        rng.gen_uint_below(&j);
    }

    #[test]
    #[should_panic]
    fn gen_int_range_zero() {
        let mut rng = rand::thread_rng();

        let b = Int::from(123);
        rng.gen_int_range(&b, &b);
    }

    #[test]
    #[should_panic]
    fn gen_int_range_negative() {
        let mut rng = rand::thread_rng();

        let lb = Int::from(123);
        let ub = Int::from(321);

        rng.gen_int_range(&ub, &lb);
    }

    #[test]
    fn gen_int_range() {
        let mut rng = rand::thread_rng();

        for _ in 0..10 {
            let i = rng.gen_int_range(&Int::from(236), &Int::from(237));
            assert_eq!(i, Int::from(236));
        }

        let l = Int::from(403469000 + 2352);
        let u = Int::from(403469000 + 3513);
        for _ in 0..1000 {
            let n: Int = rng.gen_uint_below(&u);
            assert!(n < u);

            let n: Int = rng.gen_int_range(&l, &u);
            assert!(n >= l);
            assert!(n < u);
        }
    }

    #[test]
    fn gen_uint_below_all_ones() {
        static N : &'static str =
            "000001FFFFFFFFFFFFFFFFFFFFFFFFFFF\
             FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF\
             FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF";

        let mut rng = rand::thread_rng();

        let bound = Int::from_str_radix(N, 16).unwrap();

        for _ in 0..10 {
            let n: Int = rng.gen_uint_below(&bound);
            assert!(n < bound);
        }
    }


    #[test]
    fn gcd() {
        let cases = [
            ("3", "0","3"), // special
            ("0", "3", "3"),
            ("0", "0", "0"),
            ("13", "13", "13"),
            ("37", "600", "1"), // prime numbers
            ("2567", "997", "1"),
            ("624129", "2061517", "18913"), // normal
            ("18446744073709551616", "18446744073709551616", "18446744073709551616"),
            ("184467440737095516201234", "493882992939324", "6"),
            ("493882992939324", "184467440737095516201234", "6"),
            ("18446744073709551620", "18446744073709551615", "5"),
            ("-9223372036854775808", "-9223372036854775808", "9223372036854775808"),
            ("-9223372036854775811", "-9223372036854775808", "1"),
            ("-23465475685232342344366756745345", "-23423545489322535345", "5"),
            ("-23423545489322535345", "-23465475685232342344366756745345", "5"),
            ("-170141183460469231731687303715884105728", "-170141183460469231731687303715884105729", "1"),
            ("-170141183460469231731687303715884105731", "-170141183460469231731687303715884105728", "1"),
            ("170141183460469231731687303715884105731234234363462345234345547232443500000000000000000000000", "17014118346046923173168730371588410572836362453452345000000000000000000", "5000000000000000000")
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = l.gcd(&r);
            assert_mp_eq!(val, a);
        }
    }

    #[test]
    fn lcm() {
        let cases = [
            ("1", "0", "0"),
            ("0", "1", "0"),
            ("1", "1", "1"),
            ("-1", "0", "0"),
            ("0", "-1", "0"),
            ("-1", "-1", "1"),
            ("8", "9", "72"),
            ("11", "5", "55"),
            ("99", "17", "1683"),
            ("18446744073709551616", "18446744073709551616", "18446744073709551616"),
            ("18446744073709551620", "18446744073709551615", "68056473384187692703742967930579373260"),
            ("-9223372036854775808", "-9223372036854775808", "9223372036854775808"),
            ("-9223372036854775811", "-9223372036854775808", "85070591730234615893513767968506380288"),
            ("-92233720368547758112345", "-235777694355", "4349330786055998253486590232462495")
        ];

        for &(l, r, a) in cases.iter() {
            let l : Int = l.parse().unwrap();
            let r : Int = r.parse().unwrap();
            let a : Int = a.parse().unwrap();

            let val = l.lcm(&r);
            assert_mp_eq!(val.clone(), a.clone());
        }
    }

    fn bench_add(b: &mut Bencher, xs: usize, ys: usize) {
        let mut rng = rand::thread_rng();

        let x = rng.gen_int(xs * Limb::BITS);
        let y = rng.gen_int(ys * Limb::BITS);

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

    fn bench_mul(b: &mut Bencher, xs: usize, ys: usize) {
        let mut rng = rand::thread_rng();

        let x = rng.gen_int(xs * Limb::BITS);
        let y = rng.gen_int(ys * Limb::BITS);

        b.iter(|| {
            let z = &x * &y;
            test::black_box(z);
        });
    }

    fn bench_pow(b: &mut Bencher, xs: usize, ys: usize) {
        let mut rng = rand::thread_rng();

        let x = rng.gen_int(xs * Limb::BITS);
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

    fn bench_sqr(b: &mut Bencher, xs: usize) {
        let mut rng = rand::thread_rng();

        let x = rng.gen_int(xs * Limb::BITS);

        b.iter(|| {
            let z = x.square();
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_sqr_1(b: &mut Bencher) {
        bench_sqr(b, 1);
    }

    #[bench]
    fn bench_sqr_10(b: &mut Bencher) {
        bench_sqr(b, 10);
    }

    #[bench]
    fn bench_sqr_50(b: &mut Bencher) {
        bench_sqr(b, 50);
    }

    #[bench]
    fn bench_sqr_250(b: &mut Bencher) {
        bench_sqr(b, 250);
    }

    #[bench]
    fn bench_sqr_1000(b: &mut Bencher) {
        bench_sqr(b, 1000);
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

    fn bench_div(b: &mut Bencher, xs: usize, ys: usize) {
        let mut rng = rand::thread_rng();

        let x = rng.gen_int(xs * Limb::BITS);
        let y = rng.gen_int(ys * Limb::BITS);

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

    fn bench_gcd(b: &mut Bencher, xs: usize, ys: usize) {
        let mut rng = rand::thread_rng();

        let x = rng.gen_int(xs * Limb::BITS);
        let y = rng.gen_int(ys * Limb::BITS);

        b.iter(|| {
            let z = x.gcd(&y);
            test::black_box(z);
        });
    }

    #[bench]
    fn bench_gcd_1_1(b: &mut Bencher) {
        bench_gcd(b, 1, 1);
    }

    #[bench]
    fn bench_gcd_10_10(b: &mut Bencher) {
        bench_gcd(b, 10, 10);
    }

    #[bench]
    fn bench_gcd_20_2(b: &mut Bencher) {
        bench_gcd(b, 20, 2);
    }

    #[bench]
    fn bench_gcd_50_50(b: &mut Bencher) {
        bench_gcd(b, 50, 50);
    }

    #[bench]
    fn bench_gcd_50_5(b: &mut Bencher) {
        bench_gcd(b, 50, 5);
    }

    #[bench]
    fn bench_gcd_250_150(b: &mut Bencher) {
        bench_gcd(b, 250, 150);
    }

    #[bench]
    fn bench_gcd_100_100(b: &mut Bencher) {
        bench_gcd(b, 100, 100);
    }

    #[bench]
    fn bench_gcd_100_10(b: &mut Bencher) {
        bench_gcd(b, 100, 10);
    }

    #[bench]
    fn bench_gcd_100_50(b: &mut Bencher) {
        bench_gcd(b, 100, 50);
    }

    #[bench]
    fn bench_rng_all_ones(b: &mut Bencher) {
        let mut rng = rand::thread_rng();

        let num_bits : usize = rng.gen_range(512, 1024);

        let mut bound = Int::from(1) << num_bits;
        bound -= 1;

        b.iter(|| {
            let n = rng.gen_uint_below(&bound);
            test::black_box(n);
        });
    }

}
