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

#![allow(improper_ctypes)]

use std::cmp::Ordering;

use ll;
use ll::limb::Limb;
use super::{overlap, same_or_separate, same_or_incr};
use mem;

const TOOM22_THRESHOLD : i32 = 20;

unsafe fn mul_1_generic(mut wp: *mut Limb, mut xp: *const Limb, mut n: i32, vl: Limb) -> Limb {
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
 * Multiplies the `n` least-significant limbs of `xp` by `vl` storing the `n` least-significant
 * limbs of the product in `{wp, n}`.
 *
 * Returns the highest limb of the product
 */
#[cfg(not(asm))]
#[inline]
pub unsafe fn mul_1(wp: *mut Limb, xp: *const Limb, n: i32, vl: Limb) -> Limb {
    debug_assert!(n > 0);
    debug_assert!(same_or_incr(wp, n, xp, n));

    mul_1_generic(wp, xp, n, vl)
}

/**
 * Multiplies the `n` least-significant limbs of `xp` by `vl` storing the `n` least-significant
 * limbs of the product in `{wp, n}`.
 *
 * Returns the highest limb of the product
 */
#[cfg(asm)]
#[inline]
pub unsafe fn mul_1(wp: *mut Limb, xp: *const Limb, n: i32, vl: Limb) -> Limb {
    debug_assert!(n > 0);
    debug_assert!(same_or_incr(wp, n, xp, n));
    extern "C" {
        fn ramp_mul_1(wp: *mut Limb, xp: *const Limb, n: i32, vl: Limb) -> Limb;
    }

    ramp_mul_1(wp, xp, n, vl)
}

unsafe fn addmul_1_generic(mut wp: *mut Limb, mut xp: *const Limb, mut n: i32, vl: Limb) -> Limb {
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
 * Multiplies the `n` least-signficiant digits of `xp` by `vl` and adds them to the `n`
 * least-significant digits of `wp`. Returns the highest limb of the result.
 */
#[cfg(not(asm))]
#[inline]
pub unsafe fn addmul_1(wp: *mut Limb, xp: *const Limb, n: i32, vl: Limb) -> Limb {
    addmul_1_generic(wp, xp, n, vl)
}

/**
 * Multiplies the `n` least-signficiant digits of `xp` by `vl` and adds them to the `n`
 * least-significant digits of `wp`. Returns the highest limb of the result.
 */
#[cfg(asm)]
#[inline]
pub unsafe fn addmul_1(wp: *mut Limb, xp: *const Limb, n: i32, vl: Limb) -> Limb {
    extern "C" {
        fn ramp_addmul_1(wp: *mut Limb, xp: *const Limb, n: i32, vl: Limb) -> Limb;
    }

    ramp_addmul_1(wp, xp, n, vl)
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
    debug_assert!(xs >= ys);
    debug_assert!(ys > 0);
    debug_assert!(!overlap(wp, xs + ys, xp, xs));
    debug_assert!(!overlap(wp, xs + ys, yp, ys));

    // TODO: Pick between algorithms based on input sizes
    if ys <= TOOM22_THRESHOLD {
        mul_basecase(wp, xp, xs, yp, ys);
    } else {
        let mut tmp = mem::TmpAllocator::new();
        let scratch = tmp.allocate((xs * 2) as usize);

        // Can't use xs >= (ys * 2) because if xs is odd, some other invariants
        // in toom22 don't hold
        if (xs * 2) >= (ys * 3) {
            mul_unbalanced(wp, xp, xs, yp, ys, scratch);
        } else {
            mul_toom22(wp, xp, xs, yp, ys, scratch);
        }
    }
}

unsafe fn mul_basecase(mut wp: *mut Limb, xp: *const Limb, xs: i32, mut yp: *const Limb, mut ys: i32) {

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

// Helper fn
#[inline(always)]
unsafe fn mul_rec(wp: *mut Limb,
           xp: *const Limb, xs: i32,
           yp: *const Limb, ys: i32,
           scratch: *mut Limb) {
    if ys < TOOM22_THRESHOLD {
        mul_basecase(wp, xp, xs, yp, ys);
    } else if (xs * 2) >= (ys*3) {
        mul_unbalanced(wp, xp, xs, yp, ys, scratch);
    } else {
        mul_toom22(wp, xp, xs, yp, ys, scratch);
    }
}

unsafe fn mul_toom22(wp: *mut Limb,
                     xp: *const Limb, xs: i32,
                     yp: *const Limb, ys: i32,
                     scratch: *mut Limb) {
    // Split x into x1, x0 where x = x1*(B^n) + x0
    // Split y into y1, y0 where y = y1*(B^n) + y0
    //
    // Which means the following holds:
    //
    //    x*y = (B^2n + B^n)*z2 - (B^n)*z1 + (B^n + 1)*z0
    //        = (B^2n)*z2 + (B^n)*(z2 + z0 - z1) + z0
    //
    // Where:
    //   z0 = x0*y0
    //   z1 = (x1-x0)*(y1-y0)
    //   z2 = x1*y1
    //
    // z1 is split further into:
    //
    //  zx1 = x1-x0
    //  zy1 = y1-y0
    //
    // So z1 = zx1*zy1

    debug_assert!(xs >= ys && xs < ys*2,
                  "assertion failed: `xs >= ys && xs < ys*2` xs: {}, ys: {}", xs, ys);

    let xh = xs >> 1; // Number of high limbs in x
    let nl = xs - xh; // Number of low limbs
    let yh = ys - nl; // Number of high limbs in y

    debug_assert!(0 < xh && xh <= nl);
    debug_assert!(0 < yh && yh <= xh,
                  "assertion failed: 0 < yh && yh <= xh, xs: {}, ys: {}, xh: {}, yh: {}",
                  xs, ys, xh, yh);

    let x0 = xp; // nl limbs
    let y0 = yp; // nl limbs

    let x1 = xp.offset(nl as isize); // xh limbs
    let y1 = yp.offset(nl as isize); // yh limbs

    let zx1 = wp; // nl limbs
    let zy1 = wp.offset(nl as isize); // nl limbs
    let mut z1_neg = false; // Keep track of whether the real z1 is negative

    // Calculate zx1
    if nl == xh {
        if ll::cmp(x0, x1, nl) == Ordering::Less {
            ll::sub_n(zx1, x1, x0, nl);
            z1_neg = true;
        } else {
            ll::sub_n(zx1, x0, x1, nl);
        }
    } else { // nl > xh
        if ll::is_zero(x0.offset(xh as isize), nl-xh) && ll::cmp(x0, x1, xh) == Ordering::Less {
            ll::sub_n(zx1, x1, x0, xh);
            ll::zero(zx1.offset(xh as isize), nl-xh); // Zero the extra limbs
            z1_neg = true;
        } else {
            ll::sub(zx1, x0, nl, x1, xh);
        }
    }

    // Calculate zy1
    if nl == yh {
        if ll::cmp(y0, y1, nl) == Ordering::Less {
            ll::sub_n(zy1, y1, y0, nl);
            z1_neg = !z1_neg;
        } else {
            ll::sub_n(zy1, y0, y1, nl);
        }
    } else { // nl > yh
        if ll::is_zero(y0.offset(yh as isize), nl-yh) && ll::cmp(y0, y1, yh) == Ordering::Less {
            ll::sub_n(zy1, y1, y0, yh);
            ll::zero(zy1.offset(yh as isize), nl-yh); // Zero the extra limbs
            z1_neg = !z1_neg;
        } else {
            ll::sub(zy1, y0, nl, y1, yh);
        }
    }

    let z0 = wp;
    let z1 = scratch;
    let z2 = wp.offset((nl * 2) as isize);
    let scratch_out = scratch.offset((nl * 2) as isize);

    // Calculate z1 - 2*nl limbs
    mul_rec(z1, zx1, nl, zy1, nl, scratch_out);

    // Calculate z0 - 2*nl limbs
    mul_rec(z0, x0, nl, y0, nl, scratch_out);

    // Calculate z2 - xh+yh limbs
    mul_rec(z2, x1, xh, y1, yh, scratch_out);

    // Now {wp, 2*nl} = z0 and {wp + 2*nl, xh+yh} = z2

    // {wp + nl, 2*nl} += z0 + z2 - z1
    //                 += {wp, 2*nl}
    //                  + {wp + 2*nl, xh+yh}
    //                  - z1
    //
    // So with {wp, xs+ys}:
    //
    // 0        nl      2*nl        xs+ys
    // +--------+--------+--------+---+
    // |       z0        |     z2     |
    // +--------+--------+--------+---+
    //   +      |        z0       |
    //          +--------+---+----+
    //   +      |       z2   |
    //          +------------+
    //
    // {wp + nl, nl} = HIGH(z0) + LOW(z0) + LOW(z2)
    // {wp + 2*nl, nl} = HIGH(z0) + HIGH(z2) + LOW(z2) + carry

    // LOW(z2) = HIGH(z0) + LOW(z2)
    let cy = ll::add_n(wp.offset((2*nl) as isize),
                       z2, z0.offset(nl as isize),
                       nl);

    // LOW(z0) + LOW(z2)
    let cy2 = cy + ll::add_n(wp.offset(nl as isize),
                             z0, z2,
                             nl);

    // LOW(z2) + HIGH(z2)
    let mut cy = cy + ll::add(wp.offset((2*nl) as isize),
                              z2, nl,
                              z2.offset(nl as isize), yh+xh-nl);

    // Add or subtract `z1` depending on the sign of the real result
    // (we calculate such that it's always positive, easier this way)
    if z1_neg {
        cy = cy + ll::add_n(wp.offset(nl as isize),
                       wp.offset(nl as isize), z1,
                       2*nl);
    } else {
        cy = cy - ll::sub_n(wp.offset(nl as isize),
                       wp.offset(nl as isize), z1,
                       2*nl);
    }

    // Apply the carries, has to be done last.
    ll::incr(wp.offset((nl * 2) as isize), cy2);
    ll::incr(wp.offset((nl * 3) as isize), cy);
}

/**
 * Handles multiplication when xs is much bigger than ys.
 *
 * Works basically the same way `mul_1` does, except with `ys` limbs
 * instead of a single limb.
 */
unsafe fn mul_unbalanced(mut wp: *mut Limb,
                         mut xp: *const Limb, mut xs: i32,
                         yp: *const Limb, ys: i32,
                         scratch: *mut Limb) {
    debug_assert!(xs  > ys);

    mul_toom22(wp, xp, ys, yp, ys, scratch);

    xs -= ys;
    xp = xp.offset(ys as isize);
    wp = wp.offset(ys as isize);

    // Temporary storage for the output of the multiplication
    // in the loop, the loop only needs ys*2 limbs, but the last
    // multiplication needs slightly more than that, but no more
    // than ys*3
    let mut tmp = mem::TmpAllocator::new();
    let w_tmp = tmp.allocate((ys * 3) as usize);

    while xs >= (ys * 2) {
        mul_toom22(w_tmp, xp, ys, yp, ys, scratch);
        xs -= ys;
        xp = xp.offset(ys as isize);
        let cy = ll::add_n(wp, wp, w_tmp, ys);
        ll::copy_incr(w_tmp.offset(ys as isize),
                      wp.offset(ys as isize),
                      ys);
        ll::incr(wp.offset(ys as isize), cy);

        wp = wp.offset(ys as isize);
    }

    if xs >= ys {
        mul_rec(w_tmp, xp, xs, yp, ys, scratch);
    } else {
        mul_rec(w_tmp, yp, ys, xp, xs, scratch);
    }

    let cy = ll::add_n(wp, wp, w_tmp, ys);
    ll::copy_incr(w_tmp.offset(ys as isize),
                  wp.offset(ys as isize),
                  xs);
    ll::incr(wp.offset(ys as isize), cy);
}
