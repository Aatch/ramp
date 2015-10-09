use std::cmp::Ordering;

use ll;
use ll::limb::Limb;

pub unsafe fn gcd(gp: *mut Limb, mut ap: *mut Limb, mut an: i32, mut bp: *mut Limb, mut bn: i32) -> i32 {
    assert!(an >= bn);

    let mut gc = 0;
    while *ap == 0 && !ll::is_zero(ap, an) && *bp == 0 && !ll::is_zero(bp, bn){
        ap = ap.offset(1);
        bp = bp.offset(1);
        an -= 1;
        bn -= 1;
        gc += 1;
    }

    let a_trailing = (*ap).trailing_zeros() as u32;
    let b_trailing = (*bp).trailing_zeros() as u32;

    let trailing = if a_trailing < b_trailing {
        a_trailing
    } else {
        b_trailing
    };

    if trailing > 0 {
        ll::shr(ap, ap, an, trailing);
        ll::shr(bp, bp, bn, trailing);
    }

    ll::copy_incr(bp, gp, bn);
    bp = gp;

    while !ll::is_zero(ap, an) {

        while *ap == 0 && !ll::is_zero(ap, an) {
            ap = ap.offset(1);
            an -= 1;
        }

        let at = (*ap).trailing_zeros() as u32;
        if at > 0 {
            ll::shr(ap, ap, an, at);
        }

        while *bp == 0 && !ll::is_zero(bp, bn) {
            bp = bp.offset(1);
            bn -= 1;
        }

        let bt = (*bp).trailing_zeros() as u32;
        if bt > 0 {
            ll::shr(bp, bp, bn, bt);
        }

        let c = ll::cmp(ap, bp, an);

        // FIXME find better way to compute |ap - bp| / 2
        if c == Ordering::Equal || c == Ordering::Greater {
            ll::sub(ap, ap, an, bp, bn);
            ll::shr(ap, ap, an, 1);
        } else {
            ll::sub(gp, bp, an, ap, an);
            ll::shr(gp, gp, an, 1);
            bp = gp;
        }
    }

    // FIXME what's the best way for the left shift, using offset
    let gn = (gc + 1) as i32;
    for _ in 0..gc {
        ll::shl(gp, gp, gn, (Limb::BITS - 1) as u32);
        ll::shl(gp, gp, gn, 1);
    }
    if trailing > 0 {
        ll::shl(gp, gp, gn, trailing);
    }

    gn
}
