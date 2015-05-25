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

use ll;
use ll::limb::Limb;
use super::{overlap, same_or_separate, same_or_incr};

/**
 * Multiplies the `n` least-significant limbs of `xp` by `vl` storing the `n` least-significant
 * limbs of the product in `{wp, n}`.
 *
 * Returns the highest limb of the product
 */
pub unsafe fn mul_1(mut wp: *mut Limb, mut xp: *const Limb, mut n: i32, vl: Limb) -> Limb {
    debug_assert!(n > 0);
    debug_assert!(same_or_incr(wp, n, xp, n));

    let mut cl = Limb(0);
    loop {
        let xl = *xp;
        let (hpl, lpl) = xl.mul_hilo(vl);
        let (lpl, carry) = lpl.add_overflow(cl);
        cl = hpl + carry;

        *wp = lpl;

        n -= 1;
        if n == 0 { break; }

        wp = wp.offset(1);
        xp = xp.offset(1);
    }

    return cl;
}

/**
 * Multiplies the `n` least-signficiant digits of `xp` by `vl` and adds them to the `n`
 * least-significant digits of `wp`. Returns the highest limb of the result.
 */
pub unsafe fn addmul_1(mut wp: *mut Limb, mut xp: *const Limb, mut n: i32, vl: Limb) -> Limb {
    debug_assert!(n > 0);
    debug_assert!(same_or_separate(wp, n, xp, n));

    let mut cl = Limb(0);
    loop {
        let xl = *xp;
        let (hpl, lpl) = xl.mul_hilo(vl);
        let (lpl, carry) = lpl.add_overflow(cl);
        cl = hpl + carry;

        let (lpl, carry) = (*wp).add_overflow(lpl);
        cl = cl + carry;

        *wp = lpl;

        n -= 1;
        if n == 0 { break; }

        wp = wp.offset(1);
        xp = xp.offset(1);
    }

    return cl;
}

/**
 * Multiplies the `n` least-signficiant digits of `xp` by `vl` and subtracts them from the `n`
 * least-significant digits of `wp`. Returns the highest limb of the result, adjust for borrow.
 */
pub unsafe fn submul_1(mut wp: *mut Limb, mut xp: *const Limb, mut n: i32, vl: Limb) -> Limb {
    debug_assert!(n > 0);
    debug_assert!(same_or_separate(wp, n, xp, n));

    let mut cl = Limb(0);
    loop {
        let xl = *xp;
        let (hpl, lpl) = xl.mul_hilo(vl);
        let (lpl, carry) = lpl.add_overflow(cl);
        cl = hpl + carry;

        let (lpl, carry) = (*wp).sub_overflow(lpl);
        cl = cl + carry;

        *wp = lpl;

        n -= 1;
        if n == 0 { break; }

        wp = wp.offset(1);
        xp = xp.offset(1);
    }

    return cl;
}

/**
 * Multiplies `{xp, xs}` by `{yp, ys}`, storing the result to `{wp, xs + ys}`.
 *
 * `{wp, xs + ys}` must be disjoint from both inputs.
 */
pub unsafe fn mul(wp: *mut Limb, xp: *const Limb, xs: i32, yp: *const Limb, ys: i32) {
    // TODO: Pick between algorithms based on input sizes
    mul_basecase(wp, xp, xs, yp, ys);
}

unsafe fn mul_basecase(mut wp: *mut Limb, xp: *const Limb, xs: i32, mut yp: *const Limb, mut ys: i32) {
    debug_assert!(xs >= ys);
    debug_assert!(ys > 0);
    debug_assert!(!overlap(wp, xs + ys, xp, xs));
    debug_assert!(!overlap(wp, xs + ys, yp, ys));

    *wp.offset(xs as isize) = ll::mul_1(wp, xp, xs, *yp);
    wp = wp.offset(1);
    yp = yp.offset(1);
    ys -= 1;

    while ys > 0 {
        *wp.offset(xs as isize) = ll::addmul_1(wp, xp, xs, *yp);

        wp = wp.offset(1);
        yp = yp.offset(1);
        ys -= 1;
    }
}
