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
use std::ops::{
    Add, Sub, Mul, Div, Rem, Neg,
    Shl, Shr, Not, BitAnd, BitOr, BitXor
};
use std::cmp::{Ordering, PartialEq, PartialOrd};
use std::fmt;

use std::intrinsics::assume;

macro_rules! if_cfg {
    ($(#[cfg($cfg:meta)] $it:item)+ fallback: $els:item) => (
        $(#[cfg($cfg)] $it)+
        #[cfg(not(any($($cfg),*)))] $els
    )
}

#[cfg(target_pointer_width = "32")]
pub type BaseInt = u32;
#[cfg(target_pointer_width = "64")]
pub type BaseInt = u64;

/**
 * Helper newtype for operations.
 *
 * A "Limb" is a single digit in base 2^word size.
 */
#[derive(Copy, Eq, Ord, Hash)]
pub struct Limb(pub BaseInt);

impl Clone for Limb {
    #[inline(always)]
    fn clone(&self) -> Limb { *self }
}

impl Limb {
    #[cfg(target_pointer_width = "32")]
    pub const BITS : usize = 32;
    #[cfg(target_pointer_width = "32")]
    pub const BYTES : usize = 4;
    #[cfg(target_pointer_width = "64")]
    pub const BITS : usize = 64;
    #[cfg(target_pointer_width = "64")]
    pub const BYTES : usize = 8;

    pub const B : Limb = Limb(1 << (Limb::BITS / 2));

    /// Returns the high half of the limb
    #[inline(always)]
    pub fn high_part(self) -> Limb {
        self >> (Limb::BITS / 2)
    }

    #[inline(always)]
    /// Returns the low half of the limb
    pub fn low_part(self) -> Limb {
        self & (Limb::B - 1)
    }

    /**
     * Performs `self + other`, returning the result and whether or not the addition overflowed
     */
    #[inline(always)]
    pub fn add_overflow(self, other: Limb) -> (Limb, bool) {
        unsafe {
            let (val, c) = std::intrinsics::add_with_overflow(self.0, other.0);
            (Limb(val), c)
        }
    }

    /**
     * Performs `self - other`, returning the result and whether or not the subtraction overflowed
     */
    #[inline(always)]
    pub fn sub_overflow(self, other: Limb) -> (Limb, bool) {
        unsafe {
            let (val, c) = std::intrinsics::sub_with_overflow(self.0, other.0);
            (Limb(val), c)
        }
    }

    /**
     * Performs `self * other` returning the lower half of the product
     */
    #[inline(always)]
    pub fn mul_lo(self, other: Limb) -> Limb {
        Limb(self.0.wrapping_mul(other.0))
    }

    /**
     * Performs `self * other` returning the higher half of the product
     */
    #[inline(always)]
    pub fn mul_hi(self, other: Limb) -> Limb {
        mul(self, other).0
    }

    /**
     * Performs `self * other` returning the two-limb result as (high, low).
     */
    #[inline(always)]
    pub fn mul_hilo(self, other: Limb) -> (Limb, Limb) {
        mul(self, other)
    }

    #[inline(always)]
    pub fn invert(self) -> Limb {
        debug_assert!(self.0 != 0);
        div(!self, Limb(!0), self).0
    }

    /**
     * Returns whether or not the highest bit in the limb is set.
     *
     * Division algorithms often require the highest limb of the divisor
     * to be `d >= BASE/2`.
     */
    #[inline(always)]
    pub fn high_bit_set(self) -> bool {
        (self & Limb(1 << (Limb::BITS - 1))) != 0
    }

    /**
     * Returns the number of leading zeros in the limb
     */
    #[inline(always)]
    pub fn leading_zeros(self) -> BaseInt {
        self.0.leading_zeros() as BaseInt
    }

    /**
     * Returns the number of trailing zeros in the limb
     */
    #[inline(always)]
    pub fn trailing_zeros(self) -> BaseInt {
        self.0.trailing_zeros() as BaseInt
    }

    pub unsafe fn iter_raw_bytes<'a>(&'a self) -> LimbRawBytesIteratorState<'a> {
        LimbRawBytesIteratorState {
            limb: &self,
            index: 0,
            index_back: Limb::BYTES
        }
    }

}

pub struct LimbRawBytesIteratorState<'a> {
    limb : &'a Limb,
    index : usize,
    index_back : usize,
}

impl<'a> Iterator for LimbRawBytesIteratorState<'a> {
    type Item = u8;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index == Limb::BYTES {
            return None;
        }
        let byte = ((self.limb.0 >> (self.index * 8)) & 0xFF) as u8;
        self.index += 1;
        Some(byte)
    }
}

impl<'a> DoubleEndedIterator for LimbRawBytesIteratorState<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.index_back == 0 {
            return None;
        }
        self.index_back -= 1;
        let byte : u8 = ((self.limb.0 >> (self.index_back * 8)) & 0xFF) as u8;
        Some(byte)
    }
}

impl Add<Limb> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn add(self, other: Limb) -> Limb {
        Limb(self.0.wrapping_add(other.0))
    }
}

impl Add<BaseInt> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn add(self, other: BaseInt) -> Limb {
        Limb(self.0.wrapping_add(other))
    }
}

impl Add<bool> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn add(self, other: bool) -> Limb {
        Limb(self.0.wrapping_add(other as BaseInt))
    }
}

impl Add<Limb> for BaseInt {
    type Output=Limb;

    #[inline(always)]
    fn add(self, other: Limb) -> Limb {
        Limb(self.wrapping_add(other.0))
    }
}

impl Sub<Limb> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn sub(self, other: Limb) -> Limb {
        Limb(self.0.wrapping_sub(other.0))
    }
}

impl Sub<BaseInt> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn sub(self, other: BaseInt) -> Limb {
        Limb(self.0.wrapping_sub(other))
    }
}

impl Sub<bool> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn sub(self, other: bool) -> Limb {
        Limb(self.0.wrapping_sub(other as BaseInt))
    }
}

impl Sub<Limb> for BaseInt {
    type Output=Limb;

    #[inline(always)]
    fn sub(self, other: Limb) -> Limb {
        Limb(self.wrapping_sub(other.0))
    }
}

impl Mul<Limb> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn mul(self, other: Limb) -> Limb {
        self.mul_lo(other)
    }
}

impl Mul<BaseInt> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn mul(self, other: BaseInt) -> Limb {
        Limb(self.0.wrapping_mul(other))
    }
}

impl Mul<Limb> for BaseInt {
    type Output=Limb;

    #[inline(always)]
    fn mul(self, other: Limb) -> Limb {
        Limb(self.wrapping_mul(other.0))
    }
}

impl Div<Limb> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn div(self, other: Limb) -> Limb {
        debug_assert!(other.0 != 0);
        unsafe { assume(other.0 != 0); }
        Limb(self.0 / other.0)
    }
}

impl Div<BaseInt> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn div(self, other: BaseInt) -> Limb {
        debug_assert!(other != 0);
        unsafe { assume(other != 0); }
        Limb(self.0 / other)
    }
}

impl Rem<Limb> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn rem(self, other: Limb) -> Limb {
        debug_assert!(other.0 != 0);
        unsafe { assume(other.0 != 0); }
        Limb(self.0 % other.0)
    }
}

impl Rem<BaseInt> for Limb {
    type Output=Limb;

    #[inline(always)]
    fn rem(self, other: BaseInt) -> Limb {
        debug_assert!(other != 0);
        unsafe { assume(other != 0); }
        Limb(self.0 % other)
    }
}

impl Neg for Limb {
    type Output = Limb;

    #[inline(always)]
    fn neg(self) -> Limb {
        Limb(0) - self
    }
}

impl<I> Shl<I> for Limb where BaseInt: Shl<I, Output=BaseInt> {
    type Output=Limb;

    #[inline(always)]
    fn shl(self, other: I) -> Limb {
        Limb(self.0 << other)
    }
}

impl<I> Shr<I> for Limb where BaseInt: Shr<I, Output=BaseInt> {
    type Output=Limb;

    #[inline(always)]
    fn shr(self, other: I) -> Limb {
        Limb(self.0 >> other)
    }
}

impl Not for Limb {
    type Output = Limb;

    #[inline(always)]
    fn not(self) -> Limb {
        Limb(!self.0)
    }
}

impl BitAnd<Limb> for Limb {
    type Output = Limb;

    #[inline(always)]
    fn bitand(self, other: Limb) -> Limb {
        Limb(self.0 & other.0)
    }
}

impl BitOr<Limb> for Limb {
    type Output = Limb;

    #[inline(always)]
    fn bitor(self, other: Limb) -> Limb {
        Limb(self.0 | other.0)
    }
}

impl BitXor<Limb> for Limb {
    type Output = Limb;

    #[inline(always)]
    fn bitxor(self, other: Limb) -> Limb {
        Limb(self.0 ^ other.0)
    }
}

impl PartialEq<Limb> for Limb {
    #[inline(always)]
    fn eq(&self, other: &Limb) -> bool {
        self.0 == other.0
    }

    #[inline(always)]
    fn ne(&self, other: &Limb) -> bool {
        self.0 != other.0
    }
}

impl PartialOrd<Limb> for Limb {
    #[inline(always)]
    fn partial_cmp(&self, other: &Limb) -> Option<Ordering> {
        self.0.partial_cmp(&other.0)
    }

    #[inline(always)]
    fn lt(&self, other: &Limb) -> bool { self.0 <  other.0 }

    #[inline(always)]
    fn le(&self, other: &Limb) -> bool { self.0 <= other.0 }

    #[inline(always)]
    fn gt(&self, other: &Limb) -> bool { self.0 >  other.0 }

    #[inline(always)]
    fn ge(&self, other: &Limb) -> bool { self.0 >= other.0 }
}

impl PartialEq<BaseInt> for Limb {
    #[inline(always)]
    fn eq(&self, other: &BaseInt) -> bool {
        self.0 == *other
    }

    #[inline(always)]
    fn ne(&self, other: &BaseInt) -> bool {
        self.0 != *other
    }
}

impl PartialOrd<BaseInt> for Limb {
    #[inline(always)]
    fn partial_cmp(&self, other: &BaseInt) -> Option<Ordering> {
        self.0.partial_cmp(other)
    }

    #[inline(always)]
    fn lt(&self, other: &BaseInt) -> bool { self.0 <  *other }

    #[inline(always)]
    fn le(&self, other: &BaseInt) -> bool { self.0 <= *other }

    #[inline(always)]
    fn gt(&self, other: &BaseInt) -> bool { self.0 >  *other }

    #[inline(always)]
    fn ge(&self, other: &BaseInt) -> bool { self.0 >= *other }
}

impl fmt::Debug for Limb {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl fmt::Display for Limb {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

fn mul(u: Limb, v: Limb) -> (Limb, Limb) {
    if_cfg! {
        #[cfg(target_arch="x86_64")]
        #[inline(always)]
        fn mul_impl(u: Limb, v: Limb) -> (Limb, Limb) {
            let mut high: Limb = Limb(0);
            let mut low: Limb  = Limb(0);
            unsafe {
                asm!("mulq $3"
                     : "={rdx}"(high.0), "={rax}"(low.0)
                     : "{rax}"(u.0), "r"(v.0));
            }

            (high, low)
        }

        #[cfg(target_arch="x86")]
        #[inline(always)]
        fn mul_impl(u: Limb, v: Limb) -> (Limb, Limb) {
            let mut high: Limb = Limb(0);
            let mut low: Limb  = Limb(0);
            unsafe {
                asm!("mull $3"
                     : "={edx}"(high.0), "={eax}"(low.0)
                     : "{eax}"(u.0), "r"(v.0));
            }

            (high, low)
        }

        fallback:
        #[inline(always)]
        fn mul_impl(u: Limb, v: Limb) -> (Limb, Limb) {
            let ul = u.low_part();
            let uh = u.high_part();
            let vl = v.low_part();
            let vh = v.high_part();

            let     x0 = ul * vl;
            let mut x1 = ul * vh;
            let     x2 = uh * vl;
            let mut x3 = uh * vh;

            x1 = x1 + x0.high_part();
            let (x1, c) = x1.add_overflow(x2);
            if c {
                x3 = x1 + (1 << (Limb::BITS / 2));
            }

            (x3 + x1.high_part(), (x1 << (Limb::BITS/2)) + x0.low_part())
        }
    }
    return mul_impl(u, v);
}

/**
 * Performs the two-word addition (ah, al) + (bh, bl), ignoring any overflow.
 */
#[inline(always)]
pub fn add_2(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
    if_cfg! {
        #[cfg(target_arch="x86_64")]
        #[inline(always)]
        fn add_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let mut high: Limb = Limb(0);
            let mut low: Limb  = Limb(0);
            unsafe {
                asm!("addq $4, $0
                      adcq $5, $1"
                     : "=r"(low.0), "=r"(high.0)
                     : "0"(al.0), "1"(ah.0), "r"(bl.0), "r"(bh.0));
            }

            (high, low)
        }

        #[cfg(target_arch="x86")]
        #[inline(always)]
        fn add_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let mut high: Limb = Limb(0);
            let mut low: Limb  = Limb(0);
            unsafe {
                asm!("addl $4, $0
                      adcl $5, $1"
                     : "=r"(low.0), "=r"(high.0)
                     : "0"(al.0), "1"(ah.0), "r"(bl.0), "r"(bh.0));
            }

            (high, low)
        }

        fallback:
        #[inline(always)]
        fn add_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let (low, carry) = al.add_overflow(bl);
            let high = ah + bh + carry;

            (high, low)
        }
    }
    return add_2_impl(ah, al, bh, bl);
}

/**
 * Performs the two-word subtraction (ah, al) - (bh, bl), ignoring any borrow.
 */
#[inline(always)]
pub fn sub_2(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
    if_cfg! {
        #[cfg(target_arch="x86_64")]
        #[inline(always)]
        fn sub_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let mut high: Limb = Limb(0);
            let mut low: Limb  = Limb(0);
            unsafe {
                asm!("subq $4, $0
                      sbbq $5, $1"
                     : "=r"(low.0), "=r"(high.0)
                     : "0"(al.0), "1"(ah.0), "r"(bl.0), "r"(bh.0));
            }

            (high, low)
        }

        #[cfg(target_arch="x86")]
        #[inline(always)]
        fn sub_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let mut high: Limb = Limb(0);
            let mut low: Limb  = Limb(0);
            unsafe {
                asm!("subl $4, $0
                      sbbl $5, $1"
                     : "=r"(low.0), "=r"(high.0)
                     : "0"(al.0), "1"(ah.0), "r"(bl.0), "r"(bh.0));
            }

            (high, low)
        }

        fallback:
        #[inline(always)]
        fn sub_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let (low, carry) = al.sub_overflow(bl);
            let high = ah - bh - carry;

            (high, low)
        }
    }
    return sub_2_impl(ah, al, bh, bl);
}

/**
 * Divides the two-limb numerator `(nh, nl)` by `d`, returning a single-limb
 * quotient, Q, and remainder, R, as (Q, R).
 *
 * In order to ensure a single-limb result, the following conditions are required:
 *
 * - `nh` < `d`
 * - `d` >= BASE/2
 */
#[inline(always)]
pub fn div(nh: Limb, nl: Limb, d: Limb) -> (Limb, Limb) {

    if_cfg! {
        #[cfg(target_arch="x86_64")]
        #[inline(always)]
        fn div_impl(nh: Limb, nl: Limb, d: Limb) -> (Limb, Limb) {
            let mut q: Limb = Limb(0);
            let mut r: Limb = Limb(0);
            unsafe {
                asm!("divq $4"
                     : "={rdx}"(r.0), "={rax}"(q.0)
                     : "0"(nh.0), "1"(nl.0), "r"(d.0));
            }
            (q, r)
        }

        #[cfg(target_arch="x86")]
        #[inline(always)]
        fn div_impl(nh: Limb, nl: Limb, d: Limb) -> (Limb, Limb) {
            let mut q: Limb = Limb(0);
            let mut r: Limb = Limb(0);
            unsafe {
                asm!("divl $4"
                     : "={edx}"(r.0), "={eax}"(q.0)
                     : "0"(nh.0), "1"(nl.0), "r"(d.0));
            }
            (q, r)
        }

        fallback:
        #[inline(always)]
        fn div_impl(nh: Limb, nl: Limb, d: Limb) -> (Limb, Limb) {

            let dh = d.high_part();
            let dl = d.low_part();

            let mut qh = nh / dh;
            let r1 = nh - qh * dh;
            let m = qh * dl;

            let mut r1 = r1 * (Limb::B | nl.high_part());
            if r1 < m {
                qh = qh - 1;
                let (r, carry) = r1.add_overflow(d);
                r1 = r;
                if !carry && r1 < m {
                    qh = qh - 1;
                    r1 = r1 + d;
                }
            }

            r1 = r1 - m;

            let mut ql = r1 / dh;
            let r0 = r1 - ql * dh;
            let m = ql * dl;

            let mut r0 = r0 * (Limb::B | nl.low_part());
            if r0 < m {
                ql = ql - 1;
                let (r, carry) = r0.add_overflow(d);
                r0 = r;
                if !carry && r0 < m {
                    ql = ql - 1;
                    r0 = r0 + d;
                }
            }

            r0 = r0 - m;

            (qh * (Limb::B | ql), r0)
        }
    }

    debug_assert!(d.high_bit_set());
    debug_assert!(nh < d);
    unsafe {
        assume(nh < d);
        assume(d.high_bit_set());
    }

    return div_impl(nh, nl, d);
}

/**
 * Divides `(nh, nl)` by `d` using the inverted limb `dinv`. Returns the quotient, Q, and
 * remainder, R, as (Q, R);
 */
#[inline(always)]
pub fn div_preinv(nh: Limb, nl: Limb, d: Limb, dinv: Limb) -> (Limb, Limb) {
    let (qh, ql) = dinv.mul_hilo(nh);
    let (mut qh, ql) = add_2(qh, ql, nh + 1, nl);

    let mut r = nl - qh * d;
    if r > ql {
        qh = qh - 1;
        r = r + d;
    }
    if r >= d {
        qh = qh + 1;
        r = r - d;
    }

    (qh, r)
}
