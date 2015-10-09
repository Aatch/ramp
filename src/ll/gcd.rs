use std::cmp::Ordering;

use ll;
use ll::limb::Limb;

pub unsafe fn gcd(gp: *mut Limb, mut ap: *mut Limb, mut an: i32, mut bp: *mut Limb, mut bn: i32) -> i32 {
    assert!(an >= bn);

    let mut ac = ll::scan_1(ap, an);
    let mut bc = ll::scan_1(bp, bn);

    let gc = if ac < bc {
        ac
    } else {
        bc
    };

    let mut offset = gc / Limb::BITS as u32;
    ap = ap.offset(offset as isize);
    bp = bp.offset(offset as isize);

    an -= offset as i32;
    bn -= offset as i32;

    let apbp_mod = gc % Limb::BITS as u32;
    if apbp_mod > 0 {
        ll::shr(ap, ap, an, apbp_mod);
        ll::shr(bp, bp, bn, apbp_mod);
    }

    ll::copy_incr(bp, gp, bn);
    bp = gp;

    while !ll::is_zero(ap, an) {

        ac = ll::scan_1(ap, an);
        offset = ac / Limb::BITS as u32;
        if an - offset as i32 > 0 {
            ap = ap.offset(offset as isize);
            an -= offset as i32;
        }
        let ap_mod = ac % Limb::BITS as u32;
        if ap_mod > 0 {
            ll::shr(ap, ap, an, ap_mod);
        }

        bc = ll::scan_1(bp, bn);
        offset = bc / Limb::BITS as u32;
        if bn - offset as i32 > 0 {
            bp = bp.offset(offset as isize);
            bn -= offset as i32;
        }
        let bp_mod = bc % Limb::BITS as u32;
        if bp_mod > 0 {
            ll::shr(bp, bp, bn, bp_mod);
        }

        let c = if an >= bn {
            ll::cmp(ap, bp, an)
        } else {
            ll::cmp(ap, bp, bn)
        };

        if an >= bn && (c == Ordering::Equal || c == Ordering::Greater) {
            ll::sub(ap, ap, an, bp, bn);
            ll::shr(ap, ap, an, 1);
        } else {
            ll::sub(bp, bp, an, ap, an);
            ll::shr(bp, bp, an, 1);
        }
    }

    let gn = ((gc / Limb::BITS as u32) + 1) as i32;

    for _ in 0..(gc / (Limb::BITS - 1) as u32) {
        ll::shl(gp, gp, gn, (Limb::BITS - 1) as u32);
    }
    let gc_mod = gc % (Limb::BITS - 1) as u32;
    if gc_mod > 0 {
        ll::shl(gp, gp, gn, gc_mod);
    }

    return gn;
}
