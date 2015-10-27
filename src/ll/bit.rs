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

use ll::limb::{Limb, BaseInt};
use ll::{same_or_decr, same_or_incr};

/**
 * Performs a bit-shift of the limbs in {xp, xs}, left by `cnt` bits storing the result in {rp,
 * rs}. The top-most shifted bits are returned.
 *
 * If `cnt` is greater than or equal to the number of bits in a limb, the result is undefined.
 */
pub unsafe fn shl(mut rp: *mut Limb, mut xp: *const Limb, mut xs: i32, cnt: u32) -> Limb {
    debug_assert!(xs >= 1);
    debug_assert!(cnt >= 1);
    debug_assert!(cnt < Limb::BITS as u32);
    debug_assert!(same_or_decr(rp as *const _, xs, xp, xs));

    let cnt = cnt as usize;

    rp = rp.offset((xs - 1) as isize);
    xp = xp.offset((xs - 1) as isize);

    let inv_cnt = Limb::BITS - cnt;

    let l = *xp;
    let ret = l >> inv_cnt;
    let mut high_limb = l << cnt;

    xs -= 1;
    while xs != 0 {
        xp = xp.offset(-1);
        let low = *xp;

        *rp = high_limb | (low >> inv_cnt);
        high_limb = low << cnt;

        rp = rp.offset(-1);
        xs -= 1;
    }

    *rp = high_limb;

    return ret;
}

/**
 * Performs a bit-shift of the limbs in {xp, xs}, right by `cnt` bits storing the result in {rp,
 * rs}. The bottom-most shifted bits are returned.
 *
 * If `cnt` is greater than or equal to the number of bits in a limb, the result is undefined.
 */
pub unsafe fn shr(mut rp: *mut Limb, mut xp: *const Limb, mut xs: i32, cnt: u32) -> Limb {
    debug_assert!(xs >= 1);
    debug_assert!(cnt >= 1);
    debug_assert!(cnt < Limb::BITS as u32);
    debug_assert!(same_or_incr(rp as *const _, xs, xp, xs));

    let cnt = cnt as usize;

    let inv_cnt = Limb::BITS - cnt;

    let h = *xp;
    let ret = h << inv_cnt;
    let mut low_limb = h >> cnt;

    xp = xp.offset(1);

    xs -= 1;
    while xs != 0 {
        let high = *xp;
        xp = xp.offset(1);

        *rp = low_limb | (high << inv_cnt);
        low_limb = high >> cnt;
        rp = rp.offset(1);

        xs -= 1;
    }

    *rp = low_limb;

    return ret;
}

// Common function for the operations below, since they're all essentially the same
#[inline(always)]
unsafe fn bitop<F: Fn(Limb, Limb) -> Limb>(mut wp: *mut Limb,
                                           mut xp: *const Limb, mut yp: *const Limb,
                                           n: i32, op: F) {
    debug_assert!(same_or_incr(wp, n, xp, n));
    debug_assert!(same_or_incr(wp, n, yp, n));

    let mut i = 0;
    while i < n {
        *wp = op(*xp, *yp);
        wp = wp.offset(1);
        xp = xp.offset(1);
        yp = yp.offset(1);
        i += 1;
    }
}

/**
 * Performs a bitwise "and" (`&`) of the n least signficant limbs of `xp` and `yp`, storing the
 * result in `wp`
 */
pub unsafe fn and_n(wp: *mut Limb,
                    xp: *const Limb, yp: *const Limb,
                    n: i32) {
    bitop(wp, xp, yp, n, |x, y| x & y);
}

/**
 * Performs a bitwise and of the n least signficant limbs of `xp` and `yp`, with the limbs of `yp`
 * being first inverted. The result is stored in `wp`.
 *
 * The operation is x & !y
 */
pub unsafe fn and_not_n(wp: *mut Limb,
                     xp: *const Limb, yp: *const Limb,
                     n: i32) {
    bitop(wp, xp, yp, n, |x, y| x & !y);
}

/**
 * Performs a bitwise "nand" of the n least signficant limbs of `xp` and `yp`, storing the
 * result in `wp`
 *
 * The operation is !(x & y)
 */
pub unsafe fn nand_n(wp: *mut Limb,
                     xp: *const Limb, yp: *const Limb,
                     n: i32) {
    bitop(wp, xp, yp, n, |x, y| !(x & y));
}

/**
 * Performs a bitwise "or" (`|`) of the n least signficant limbs of `xp` and `yp`, storing the
 * result in `wp`
 */
pub unsafe fn or_n(wp: *mut Limb,
                    xp: *const Limb, yp: *const Limb,
                    n: i32) {
    bitop(wp, xp, yp, n, |x, y| x | y);
}

/**
 * Performs a bitwise "or" of the n least signficant limbs of `xp` and `yp`, with the limbs of `yp`
 * being first inverted. The result is stored in `wp`.
 */
pub unsafe fn or_not_n(wp: *mut Limb,
                    xp: *const Limb, yp: *const Limb,
                    n: i32) {
    bitop(wp, xp, yp, n, |x, y| x | !y);
}

/**
 * Performs a bitwise "nor" of the n least signficant limbs of `xp` and `yp`, storing the
 * result in `wp`
 *
 * The operation is !(x | y)
 */
pub unsafe fn nor_n(wp: *mut Limb,
                    xp: *const Limb, yp: *const Limb,
                    n: i32) {
    bitop(wp, xp, yp, n, |x, y| !(x | y));
}

/**
 * Performs a bitwise "xor" (`^`) of the n least signficant limbs of `xp` and `yp`, storing the
 * result in `wp`
 */
pub unsafe fn xor_n(wp: *mut Limb,
                    xp: *const Limb, yp: *const Limb,
                    n: i32) {
    bitop(wp, xp, yp, n, |x, y| x ^ y);
}

/**
 * Performs a bitwise inversion ("not") of the n least signficant limbs of `xp`, storing the
 * result in `wp`
 */
pub unsafe fn not(mut wp: *mut Limb, mut xp: *const Limb, n: i32) {
    debug_assert!(same_or_incr(wp, n, xp, n));

    let mut i = 0;
    while i < n {
        *wp = !*xp;
        wp = wp.offset(1);
        xp = xp.offset(1);
        i += 1;
    }
}

/**
 * Computes the two's complement of the `xs` least significant words
 * of `xp`. The result is stored the result in `wp`, and a carry is
 * returned, if there is one.
 */
pub unsafe fn twos_complement(mut wp: *mut Limb, mut xp: *mut Limb, xs: i32) -> Limb {
    let mut i = 0;
    let mut carry = Limb(1);

    while i < xs {
        let flipped = !*xp;
        *wp = flipped + carry;
        xp = xp.offset(1);
        wp = wp.offset(1);
        i += 1;
        carry = carry & Limb((flipped == !0) as BaseInt);
    }

    carry
}

/**
 * Scans for the first 1 bit starting from the least-significant bit the the most, returning
 * the bit index.
 */
pub unsafe fn scan_1(mut xp: *const Limb, mut xs: i32) -> u32 {
    debug_assert!(xs > 0);
    let mut cnt = 0u32;

    while *xp == 0 {
        cnt += Limb::BITS as u32;
        xp = xp.offset(1);
        xs -= 1;
        if xs == 0 { return cnt; }
    }
    cnt += (*xp).trailing_zeros() as u32;

    return cnt;
}

/**
 * Scans for the first 0 bit starting from the least-significant bit the the most, returning
 * the bit index.
 */
pub unsafe fn scan_0(mut xp: *const Limb, mut xs: i32) -> u32 {
    debug_assert!(xs > 0);
    let mut cnt = 0u32;

    while *xp == !0 {
        cnt += Limb::BITS as u32;
        xp = xp.offset(1);
        xs -= 1;
        if xs == 0 { return cnt; }
    }
    let mut last = (*xp).0;
    while last & 1 != 0 {
        cnt += 1;
        last >>= 1;
    }

    return cnt;
}
