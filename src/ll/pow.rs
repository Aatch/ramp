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
use mem;

/**
 * Takes `{ap, an}` to the power of `exp` and stores the result in `{wp, an*exp}`.
 *
 * `{wp, an*exp}` must be disjoint from `{ap, an}`.
 * `{ap, an}` must not be zero.
 * `exp` must be greater than 2
 */
pub unsafe fn pow(mut wp: *mut Limb, mut ap: *const Limb, mut an: i32, mut exp: u32) {
    debug_assert!(exp > 2);
    debug_assert!(!ll::is_zero(ap, an));
    debug_assert!(!ll::overlap(wp, an*exp as i32, ap, an));

    let mut tmp = mem::TmpAllocator::new();

    ll::zero(wp, an * (exp as i32));

    while *ap == 0 {
        ap = ap.offset(1);
        wp = wp.offset(1);
        an -= 1;
    }
    let trailing = (*ap).trailing_zeros() as u32;

    // Calculate the size we need to store the base and the scratch space
    // The number of limbs is going to be the number of limbs in the (shifted) ap
    // multiplied by the exponent (due to x*x having up to twice as many digits as x)
    let sz = (an * (exp as i32)) as usize;
    let (bp, scratch) = tmp.allocate_2(sz, sz);
    let mut bn = an;

    if trailing > 0 {
        ll::shr(bp, ap, an, trailing);
    } else {
        ll::copy_incr(ap, bp, an);
    }

    // Calculate the amount we'll need to shift by at the end,
    // we need to adjust wp here because the shift functions only
    // work with shifts of < Limb::BITS
    let mut shift = trailing * exp;
    while shift >= Limb::BITS as u32 {
        shift -= Limb::BITS as u32;
        wp = wp.offset(1);
    }

    *wp = Limb(1);
    let mut wn = 1;

    loop {
        if (exp & 1) == 1 {
            if wn > bn {
                ll::mul(scratch, wp, wn, bp, bn);
            } else {
                ll::mul(scratch, bp, bn, wp, wn);
            }
            wn = ll::normalize(scratch, wn + bn);
            ll::copy_incr(scratch, wp, wn);
        }

        exp >>= 1;

        // Do this check before the base multiplication so we don't
        // end up needing more space than necessary
        if exp == 0 {
            break;
        }

        ll::mul(scratch, bp, bn, bp, bn);
        bn = ll::normalize(scratch, bn + bn);

        ll::copy_incr(scratch, bp, bn);

    }

    if shift > 0 {
        let v = ll::shl(wp, wp, wn+1, shift);
        debug_assert!(v == 0);
    }
}
