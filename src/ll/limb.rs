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

use ::std::num::Wrapping;
#[allow(dead_code)]
type Word = Wrapping<usize>;

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
    #[cfg(target_pointer_width = "64")]
    pub const BITS : usize = 64;

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

pub fn mul(u: Limb, v: Limb) -> (Limb, Limb) {
    if_cfg! {
        #[cfg(all(not(feature="fallbacks"),target_arch="x86_64"))]
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

        #[cfg(all(not(feature="fallbacks"),target_arch="x86"))]
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

        #[cfg(all(  not(feature="fallbacks"),
                    not(target_arch="x86"),
                    target_pointer_width="32",
            ))]
        #[inline(always)]
        fn mul_impl(u: Limb, v: Limb) -> (Limb, Limb) {
            let u = u.0 as u64;
            let v = v.0 as u64;
            let p = u*v;
            (Limb((p>>32) as u32), Limb(p as u32))
        }

        fallback:
        #[inline(always)]
        fn mul_impl(u: Limb, v: Limb) -> (Limb, Limb) {
            fn mul_2_usize_to_2_usize(u:Word, v: Word) -> (Word,Word) {
                // see http://www.hackersdelight.org/hdcodetxt/muldwu.c.txt
                const BITS:usize = Limb::BITS / 2;
                const LO_MASK:Word = Wrapping((1usize << BITS) - 1);

                let u0 = u >> BITS;
                let u1 = u & LO_MASK;
                let v0 = v >> BITS;
                let v1 = v & LO_MASK;

                let t = u1 * v1;
                let w3 = t & LO_MASK;
                let k = t >> BITS;

                let t = u0*v1 + k;
                let w2 = t & LO_MASK;
                let w1 = t >> BITS;

                let t = u1 * v0 + w2;
                let k = t >> BITS;

                (u0*v0+w1+k, (t<<BITS) + w3)
            }

            let (h,l) = mul_2_usize_to_2_usize(
                Wrapping(u.0 as usize),
                Wrapping(v.0 as usize));

            (Limb(h.0 as BaseInt), Limb(l.0 as BaseInt))

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
        #[cfg(all(not(feature="fallbacks"),target_arch="x86_64"))]
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

        #[cfg(all(not(feature="fallbacks"),target_arch="x86"))]
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

        #[inline(always)]
        #[cfg(all(  not(feature="fallbacks"),
                    not(target_arch="x86"),
                    target_pointer_width="32",
            ))]
        fn add_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let a = ((ah.0 as u64) << 32) | al.0 as u64;
            let b = ((bh.0 as u64) << 32) | bl.0 as u64;
            let s = a.overflowing_add(b).0;
            (Limb((s>>32) as u32), Limb(s as u32))
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
        #[cfg(all(not(feature="fallbacks"),target_arch="x86_64"))]
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

        #[cfg(all(not(feature="fallbacks"),target_arch="x86"))]
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

        #[cfg(all(  not(feature="fallbacks"),
                    not(target_arch="x86"),
                    target_pointer_width="32",
            ))]
        #[inline(always)]
        fn sub_2_impl(ah: Limb, al: Limb, bh: Limb, bl: Limb) -> (Limb, Limb) {
            let a = ((ah.0 as u64) << 32) | al.0 as u64;
            let b = ((bh.0 as u64) << 32) | bl.0 as u64;
            let s = a.overflowing_sub(b).0;
            (Limb((s>>32) as u32), Limb(s as u32))
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
        #[cfg(all(not(feature="fallbacks"),target_arch="x86_64"))]
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

        #[cfg(all(not(feature="fallbacks"),target_arch="x86"))]
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

        #[cfg(all(  not(feature="fallbacks"),
                    not(target_arch="x86"),
                    target_pointer_width="32",
            ))]
        #[inline(always)]
        fn div_impl(nh: Limb, nl: Limb, d: Limb) -> (Limb, Limb) {
            let n = (nh.0 as u64) << 32 | nl.0 as u64;
            let d = d.0 as u64;
            (Limb((n/d) as u32), Limb((n%d) as u32))
        }

        fallback:
        #[inline(always)]
        fn div_impl(nh: Limb, nl: Limb, d: Limb) -> (Limb, Limb) {
            fn div_2_usize_by_usize(u1:Word, u0: Word, v: Word) -> (Word,Word) {
                // See http://www.hackersdelight.org/hdcodetxt/divlu.c.txt (last one)
                // s == 0 in our case, d normalization is already done
                const BITS:usize = Limb::BITS / 2;
                const ONE:Word = Wrapping(1usize);
                const B:Word = Wrapping(1usize << BITS);
                const LO_MASK:Word = Wrapping((1usize << BITS) - 1);

                let vn1 = v >> BITS;
                let vn0 = v & LO_MASK;

                let un32 = u1;
                let un10 = u0;

                let un1 = un10 >> BITS;
                let un0 = un10 & LO_MASK;

                let mut q1 = un32 / vn1;
                let mut rhat = un32 - q1*vn1;

                while q1 >= B || q1*vn0 > B*rhat + un1 {
                    q1 -= ONE;
                    rhat += vn1;
                    if rhat >= B {
                        break;
                    }
                }

                let un21 = un32*B +un1 - q1*v;

                let mut q0 = un21 / vn1;
                let mut rhat = un21 - q0*vn1;
                while q0 >= B || q0*vn0 > B*rhat + un0 {
                    q0 -= ONE;
                    rhat += vn1;
                    if rhat >= B {
                        break;
                    }
                }
                (q1*B + q0, un21*B + un0 - q0*v)
            }

            let (q,r) = div_2_usize_by_usize(
                Wrapping(nh.0 as usize),
                Wrapping(nl.0 as usize),
                Wrapping(d.0 as usize));

            (Limb(q.0 as BaseInt), Limb(r.0 as BaseInt))
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

#[test]
fn test_bug_div_1() {
    let (q,r) = div(Limb(0), Limb(10), Limb((usize::max_value()/2+1) as BaseInt));
    assert_eq!((q.0, r.0), (0, 10));
}

#[cfg(target_pointer_width = "64")]
#[test]
fn test_bug_mul_1() {
    let (h,l) = mul(Limb(18446744073709551615), Limb(7868907223611932671));
    assert_eq!((h.0,l.0), (7868907223611932670, 10577836850097618945));
}
