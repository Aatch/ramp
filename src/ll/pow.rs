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

use ll::limb_ptr::{Limbs, LimbsMut};

/**
 * Takes `{ap, an}` to the power of `exp` and stores the result to `wp`. `wp` is
 * assumed to have enough space to store the result (which can be calculated using
 * `num_pow_limbs`
 *
 * `{wp, an*exp}` must be disjoint from `{ap, an}`.
 * `{ap, an}` must not be zero.
 * `exp` must be greater than 2
 */
pub unsafe fn pow(mut wp: LimbsMut, mut ap: Limbs, mut an: i32, mut exp: u32) {
    debug_assert!(exp > 2);
    debug_assert!(!ll::is_zero(ap, an));

    let mut wn = num_pow_limbs(ap, an, exp);
    debug_assert!(!ll::overlap(wp, wn, ap, an));

    let mut tmp = mem::TmpAllocator::new();

    ll::zero(wp, wn);

    // (m * 2**K)**exp == m**exp * 2**(K*exp)
    while *ap == 0 {
        ap = ap.offset(1);
        an -= 1;
        wp = wp.offset(exp as isize);
        wn -= exp as i32;
    }
    let trailing = (*ap).trailing_zeros() as u32;

    let sz = wn as usize;

    // An extra limb of scratch space is needed because the length
    // estimation is precise: if you're doing something like x**7, the
    // final multiplication is ``x**3 * x**4`. These could have
    // lengths, like, say, 30 and 40 limbs, so the multiplication can
    // take at most 30 + 40 + 1 limbs, and the multiplication
    // algorithm will write to all of them, possibly putting a zero in
    // the very highest limb... however, the x**7 length estimator may
    // work out that the final result actually fits into only 70
    // limbs, so if we don't account for this mismatch we risk memory
    // corruption.
    //
    // (Examples of such x are 2**(k L), where k > 0 is an integer and
    // L is the number of bits in a limb.)
    let (bp, scratch) = tmp.allocate_2(sz, sz + 1);
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
                ll::mul(scratch, wp.as_const(), wn, bp.as_const(), bn);
            } else {
                ll::mul(scratch, bp.as_const(), bn, wp.as_const(), wn);
            }
            wn = ll::normalize(scratch.as_const(), wn + bn);
            ll::copy_incr(scratch.as_const(), wp, wn);
        }

        exp >>= 1;

        // Do this check before the base multiplication so we don't
        // end up needing more space than necessary
        if exp == 0 {
            break;
        }

        ll::sqr(scratch, bp.as_const(), bn);
        bn = ll::normalize(scratch.as_const(), bn + bn);

        ll::copy_incr(scratch.as_const(), bp, bn);

    }

    if shift > 0 {
        let v = ll::shl(wp, wp.as_const(), wn, shift);
        if v > 0 {
            *wp.offset(wn as isize) = v;
        }
    }
}

/// Calculates the number of limbs required to store the result of taking
/// `{xp, xn}` to the power of `exp`
pub unsafe fn num_pow_limbs(xp: Limbs, xn: i32, exp: u32) -> i32 {
    // This is a better approximation of log_b(x^e) than simply using the
    // the number of digits, n.
    // Instead it uses the most significant digit, a, to calculate
    // e*log_b(a*b^(n-1)), which is e*(log_b(a) + n - 1)
    let n = xn - 1;
    let high_limb = *xp.offset(n as isize);

    // Calculate log_2(a), this is because floor(log_b(a)) will always be
    // 0
    let lg2 = Limb::BITS as u32 - high_limb.leading_zeros() as u32;

    // Get e*log_2(a)
    let lg2e = exp as i32 * lg2 as i32;

    // Now convert it to log_b using the formula
    // log_a(x) = log_b(x) / log_b(a)
    let elog_b = lg2e / Limb::BITS as i32;

    // Add a final 1 to account for the error in the estimate
    elog_b + (exp as i32 * n) + 1
}
