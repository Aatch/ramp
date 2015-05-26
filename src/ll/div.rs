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

use std::intrinsics::assume;
use std::cmp::Ordering;

use mem;
use ll;
use ll::limb::{self, Limb};
use super::{same_or_separate, overlap};

/**
 * Divides the `xs` least-significant limbs at `xp` by `d`, storing the result in {qp, qxn + xs}.
 *
 * Specifically, the integer part is stored in {qp+qxn, xs} and the fractional part (if any) is
 * stored in {qp, qxn}. The remainder is returned.
 */
pub unsafe fn divrem_1(mut qp: *mut Limb, qxn: i32,
                       xp: *const Limb, mut xs: i32, d: Limb) -> Limb {
    debug_assert!(qxn >= 0);
    debug_assert!(xs >= 0);
    debug_assert!(d != 0);
    debug_assert!(same_or_separate(qp.offset(qxn as isize) as *const _, xs, xp, xs));

    assume(qxn >= 0);
    assume(xs >= 0);
    assume(d != 0);

    let mut n = xs + qxn;
    if n == 0 { return Limb(0); }

    qp = qp.offset((n - 1) as isize);

    let mut r = Limb(0);
    if d.high_bit_set() {
        if xs != 0 {
            r = *xp.offset((xs - 1) as isize);
            let q = if r >= d { Limb(1) } else { Limb(0) };
            *qp = q;
            qp = qp.offset(-1);
            r = r - (d & -q);
            xs -= 1;
        }

        let dinv = d.invert();
        let mut i = xs - 1;
        while i >= 0 {
            let n0 = *xp.offset(i as isize);
            let (q, rem) = limb::div_preinv(r, n0, d, dinv);
            r = rem;
            *qp = q;
            qp = qp.offset(-1);
            i -= 1;
        }
        let mut i = qxn - 1;
        while i >= 0 {
            let (q, rem) = limb::div_preinv(r, Limb(0), d, dinv);
            r = rem;
            *qp = q;
            qp = qp.offset(-1);
            i -= 1;
        }

        return r;
    } else {
        if xs != 0 {
            let n1 = *xp.offset((xs - 1) as isize);
            if n1 < d {
                r = n1;
                *qp = Limb(0);
                qp = qp.offset(-1);
                n -= 1;
                if n == 0 {
                    return r;
                }
                xs -= 1;
            }
        }

        let cnt = d.leading_zeros() as usize;

        let d = d << cnt;
        r = r << cnt;

        let dinv = d.invert();
        if xs != 0 {
            let mut n1 = *xp.offset((xs - 1) as isize);
            r = r | (n1 >> (Limb::BITS - cnt));
            let mut i = xs - 2;
            while i >= 0 {
                let n0 = *xp.offset(i as isize);
                let nshift = (n1 << cnt) | (n0 >> (Limb::BITS - cnt));
                let (q, rem) = limb::div_preinv(r, nshift, d, dinv);

                r = rem;
                *qp = q;

                qp = qp.offset(-1);
                n1 = n0;
                i -= 1;
            }
            let (q, rem) = limb::div_preinv(r, n1 << cnt, d, dinv);
            r = rem;
            *qp = q;
            qp = qp.offset(-1);
        }

        let mut i = qxn - 1;
        while i >= 0 {
            let (q, rem) = limb::div_preinv(r, Limb(0), d, dinv);
            r = rem;
            *qp = q;

            qp = qp.offset(-1);
            i -= 1;
        }

        return r >> cnt;
    }
}

/**
 * Divides {np, ns} by {dp, ds}. If ns <= ds, the quotient is stored in {qp, 1}, otherwise
 * the quotient is stored to {qp, (ns - ds) + 1}. The remainder is always stored to {rp, ds}.
 */
pub unsafe fn divrem(qp: *mut Limb, rp: *mut Limb,
                     np: *const Limb, ns: i32,
                     dp: *const Limb, ds: i32) {
    debug_assert!(!overlap(qp, (ns - ds) + 1, np, ns));

    if ns < ds {
        *qp = Limb(0);
        ll::copy_incr(np, rp, ns);
        return;
    } else if ns == ds {
        if let Ordering::Less = ll::cmp(np, dp, ns) {
            *qp = Limb(0);
            ll::copy_incr(np, rp, ns);
            return;
        }
    }

    match ds {
        1 => {
            let r = divrem_1(qp, 0, np, ns, *dp);
            *rp = r;
        }
        _ => {
            let mut tmp = mem::TmpAllocator::new();

            let dh = *dp.offset((ds - 1) as isize);

            let cnt = dh.leading_zeros() as u32;
            let dp_tmp;
            let np_tmp;
            let mut ns_tmp = ns;

            if cnt == 0 {
                dp_tmp = dp;
                np_tmp = tmp.allocate(ns_tmp as usize);
                ll::copy_incr(np, np_tmp, ns);
            } else {
                ns_tmp += 1;
                np_tmp = tmp.allocate(ns_tmp as usize);

                let c = ll::shl(np_tmp, np, ns, cnt);
                if c > 0 {
                    *np_tmp.offset(ns as isize) = c;
                } else {
                    ns_tmp -= 1;
                }

                let dtmp = tmp.allocate(ds as usize);
                ll::shl(dtmp, dp, ds, cnt);
                dp_tmp = dtmp;
            }

            let qh = sb_div(qp, np_tmp, ns_tmp, dp_tmp, ds);
            if qh > 0 {
                *qp.offset((ns - ds) as isize) = qh;
            }

            if cnt == 0 {
                ll::copy_incr(np_tmp, rp, ds);
            } else {
                ll::shr(rp, np_tmp, ds, cnt);
            }
        }
    }

}

/**
 * "Schoolbook" division of two unsigned integers, N, D, producing Q = floor(N/D).
 * The return value is the highest limb of the quotient, which may be zero.
 * Specifically, it divides the `ns` least significant limbs of N by the `ds` least
 * significant limbs of `D`, writing ns - ds limbs of quotient to qp.
 *
 * The limbs stored in `np` are modified and the lowest `ds` limbs contain the remainder
 * of the division.
 *
 * The denominator is assumed to conform to the follow restrictions (where B is the base):
 *
 *   1. D < N
 *   2. Most significant limb of D is >= floor(B/2).
 *
 * It is also assumed that `ns >= ds`.
 */
unsafe fn sb_div(qp: *mut Limb,
                 np: *mut Limb, ns: i32,
                 dp: *const Limb, ds: i32) -> Limb {
    debug_assert!(ds > 1);
    debug_assert!(ns >= ds);
    debug_assert!((*dp.offset((ds - 1) as isize)).high_bit_set());

    let mut np = np.offset(ns as isize);

    // If N < D*B^(m-n-1), then the high limb is zero. If not, then the high limb
    // is 1 and we subtract D*B^(m-n-1) from N.
    let qh = if let Ordering::Less = ll::cmp(np.offset(-ds as isize), dp, ds) {
        Limb(0)
    } else {
        let np = np.offset(-ds as isize);
        ll::sub_n(np, np, dp, ds);
        Limb(1)
    };

    let mut qp = qp.offset((ns - ds) as isize);

    let ds = (ds - 1) as isize;
    let d = *dp.offset(ds);

    np = np.offset(-1);
    let mut nh = *np;

    let mut i = ns - (ds + 1) as i32;
    while i > 0 {
        np = np.offset(-1);

        let nl = *np;

        let q = if nh == d {
            ll::submul_1(np.offset(-ds), dp, (ds + 1) as i32, Limb(!0));
            nh = *np;
            Limb(!0)
        } else {
            let (q, r) = limb::div(nh, nl, d);
            let c = ll::submul_1(np.offset(-ds), dp, ds as i32, q);

            nh = r - c;

            if r < c {
                nh = nh + ll::add_n(np.offset(-ds), np.offset(-ds), dp, (ds + 1) as i32);
                q - 1
            } else {
                q
            }
        };

        qp = qp.offset(-1);
        *qp = q;

        i -= 1;
    }

    *np = nh;

    return qh;
}
