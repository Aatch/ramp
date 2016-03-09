// Copyright 2016 The Ramp Developers
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

use std::cmp::Ordering;

use ll;
use ll::limb_ptr::LimbsMut;

pub unsafe fn gcd(mut gp: LimbsMut, mut ap: LimbsMut, mut an: i32, mut bp: LimbsMut, mut bn: i32) -> i32 {
    assert!(an >= bn);

    let mut gc = 0;
    while *ap == 0 && !ll::is_zero(ap.as_const(), an)
        && *bp == 0 && !ll::is_zero(bp.as_const(), bn) {
        ap = ap.offset(1);
        bp = bp.offset(1);
        gp = gp.offset(1);
        an -= 1;
        bn -= 1;
        gc += 1;
    }

    let a_trailing = (*ap).trailing_zeros() as u32;
    let b_trailing = (*bp).trailing_zeros() as u32;

    let trailing = if a_trailing <= b_trailing {
        a_trailing
    } else {
        b_trailing
    };
    if trailing > 0 {
        ll::shr(ap, ap.as_const(), an, trailing);
        ll::shr(bp, bp.as_const(), bn, trailing);
    }

    while !ll::is_zero(ap.as_const(), an) {

        while *ap == 0 && !ll::is_zero(ap.as_const(), an) {
            ap = ap.offset(1);
            an -= 1;
        }

        let at = (*ap).trailing_zeros() as u32;
        if at > 0 {
            ll::shr(ap, ap.as_const(), an, at);
        }

        while *bp == 0 && !ll::is_zero(bp.as_const(), bn) {
            bp = bp.offset(1);
            bn -= 1;
        }

        let bt = (*bp).trailing_zeros() as u32;
        if bt > 0 {
            ll::shr(bp, bp.as_const(), bn, bt);
        }

        an = ll::normalize(ap.as_const(), an);
        bn = ll::normalize(bp.as_const(), bn);

        let c = if an == bn {
            ll::cmp(ap.as_const(), bp.as_const(), an)
        } else if an > bn {
            Ordering::Greater
        } else {
            Ordering::Less
        };

        if c == Ordering::Greater || c == Ordering::Equal  {
            ll::sub(ap, ap.as_const(), an, bp.as_const(), bn);
            ll::shr(ap, ap.as_const(), an, 1);
        } else {
            ll::sub(bp, bp.as_const(), bn, ap.as_const(), an);
            ll::shr(bp, bp.as_const(), bn, 1);
        }
    }

    ll::copy_incr(bp.as_const(), gp, bn);

    if trailing > 0 {
        let v = ll::shl(gp, gp.as_const(), bn, trailing);
        if v > 0 {
            *gp.offset(bn as isize) = v;
        }
    }

    gc + bn
}
