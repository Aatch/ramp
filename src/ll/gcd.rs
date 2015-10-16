use std::cmp::Ordering;

use ll;
use ll::limb::Limb;

pub unsafe fn gcd(mut gp: *mut Limb, mut ap: *mut Limb, mut an: i32, mut bp: *mut Limb, mut bn: i32) -> i32 {
    assert!(an >= bn);

    let mut gc = 0;
    while *ap == 0 && !ll::is_zero(ap, an) && *bp == 0 && !ll::is_zero(bp, bn){
        ap = ap.offset(1);
        bp = bp.offset(1);
        gp = gp.offset(1);
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

        if c == Ordering::Equal || c == Ordering::Greater {
            ll::sub(ap, ap, an, bp, bn);
            ll::shr(ap, ap, an, 1);
        } else {
            ll::sub(gp, bp, bn, ap, bn);
            ll::shr(gp, gp, bn, 1);
            bp = gp;
        }
    }

    if trailing > 0 {
        let v = ll::shl(gp, gp, bn, trailing);
        if v > 0 {
            *gp.offset(bn as isize) = v;
            gc += 1;
        }
    }

    gc + bn
}
