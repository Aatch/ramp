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

use ll::limb::Limb;
use super::{copy_rest, same_or_separate};

/**
 * Adds the `n` least signficant limbs of `xp` and `yp`, storing the result in {wp, n}.
 * If there was a carry, it is returned.
 */
pub unsafe fn add_n(mut wp: *mut Limb, mut xp: *const Limb, mut yp: *const Limb,
                    mut n: i32) -> Limb {
    let mut carry = Limb(0);

    debug_assert!(n >= 1);
    debug_assert!(same_or_separate(wp as *const _, n, xp, n));
    debug_assert!(same_or_separate(wp as *const _, n, yp, n));

    loop {
        let xl = *xp;
        let yl = *yp;

        let (sl, c1) = xl.add_overflow(yl);
        let (rl, c2) = sl.add_overflow(carry);

        carry = if c1 || c2 { Limb(1) } else { Limb(0) };
        *wp = rl;

        n -= 1;
        if n == 0 { break; }

        wp = wp.offset(1);
        xp = xp.offset(1);
        yp = yp.offset(1);

    }

    carry
}

/**
 * Subtracts the `n` least signficant limbs of `yp` from `xp`, storing the result in {wp, n}.
 * If there was a borrow from a higher-limb (i.e., the result would be negative), it is returned.
 */
pub unsafe fn sub_n(mut wp: *mut Limb, mut xp: *const Limb, mut yp: *const Limb,
                    mut n: i32) -> Limb {
    let mut carry = Limb(0);

    debug_assert!(n >= 1);
    debug_assert!(same_or_separate(wp as *const _, n, xp, n));
    debug_assert!(same_or_separate(wp as *const _, n, yp, n));

    loop {
        let xl = *xp;
        let yl = *yp;

        let (sl, c1) = xl.sub_overflow(yl);
        let (rl, c2) = sl.sub_overflow(carry);

        carry = if c1 || c2 { Limb(1) } else { Limb(0) };
        *wp = rl;

        n -= 1;
        if n == 0 { break; }

        wp = wp.offset(1);
        xp = xp.offset(1);
        yp = yp.offset(1);

    }

    carry
}

macro_rules! aors {
    ($op:ident, $lop:ident, $f:ident) => {
        #[inline]
        pub unsafe fn $op(wp: *mut Limb,
                          xp: *const Limb, xs: i32,
                          yp: *const Limb, ys: i32) -> Limb {

            debug_assert!(xs >= ys);
            debug_assert!(ys >= 0);

            let mut i = ys;
            let carry = $f(wp, xp, yp, ys);
            if carry == 1 {
                loop {
                    if i >= xs { return Limb(1); }

                    let (x, carry) = Limb::$lop(*xp.offset(i as isize), Limb(1));
                    *wp.offset(i as isize) = x;
                    i += 1;
                    if !carry {
                        break;
                    }
                }
            }

            if wp as *const Limb != xp && i < xs {
                copy_rest(xp, wp, xs, i);
            }

            return Limb(0);
        }
    }
}

aors!(add, add_overflow, add_n);
aors!(sub, sub_overflow, sub_n);

macro_rules! aors_1 {
    ($op:ident, $f:ident) => {
        #[inline]
        pub unsafe fn $op(wp: *mut Limb,
                          xp: *const Limb, xs: i32,
                          y: Limb) -> Limb {

            if xs > 0 {
                let (v, mut carry) = Limb::$f(*xp, y);
                *wp = v;
                let mut i = 1;
                while carry {
                    if i >= xs { return Limb(1); }

                    let (v, c) = Limb::$f(*xp.offset(i as isize), Limb(1));
                    carry = c;
                    *wp.offset(i as isize) = v;
                    i += 1;
                }
            }
            return Limb(0);
        }
    }
}

aors_1!(add_1, add_overflow);
aors_1!(sub_1, sub_overflow);
