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
use ll::{same_or_decr, same_or_incr};

/**
 * Performs a bit-shift of the limbs in {xp, xs}, left by `cnt` bits storing the result in {rp,
 * rs}. The top-most shifted bits are returned.
 *
 * If `cnt` is greater than or equal to the number of bits in a limb, the result is undefined.
 */
pub unsafe fn shl(mut rp: *mut Limb, mut xp: *const Limb, mut xs: i32, cnt: u32) -> Limb {
    debug_assert!(xs >= 1);
    debug_assert!(cnt >= 1);
    debug_assert!(cnt < Limb::BITS as u32);
    debug_assert!(same_or_decr(rp as *const _, xs, xp, xs));

    let cnt = cnt as usize;

    rp = rp.offset((xs - 1) as isize);
    xp = xp.offset((xs - 1) as isize);

    let inv_cnt = Limb::BITS - cnt;

    let l = *xp;
    let ret = l >> inv_cnt;
    let mut high_limb = l << cnt;

    xs -= 1;
    while xs != 0 {
        xp = xp.offset(-1);
        let low = *xp;

        *rp = high_limb | (low >> inv_cnt);
        high_limb = low << cnt;

        rp = rp.offset(-1);
        xs -= 1;
    }

    *rp = high_limb;

    return ret;
}

/**
 * Performs a bit-shift of the limbs in {xp, xs}, right by `cnt` bits storing the result in {rp,
 * rs}. The bottom-most shifted bits are returned.
 *
 * If `cnt` is greater than or equal to the number of bits in a limb, the result is undefined.
 */
pub unsafe fn shr(mut rp: *mut Limb, mut xp: *const Limb, mut xs: i32, cnt: u32) -> Limb {
    debug_assert!(xs >= 1);
    debug_assert!(cnt >= 1);
    debug_assert!(cnt < Limb::BITS as u32);
    debug_assert!(same_or_incr(rp as *const _, xs, xp, xs));

    let cnt = cnt as usize;

    let inv_cnt = Limb::BITS - cnt;

    let h = *xp;
    let ret = h << inv_cnt;
    let mut low_limb = h >> cnt;

    xp = xp.offset(1);

    xs -= 1;
    while xs != 0 {
        let high = *xp;
        xp = xp.offset(1);

        *rp = low_limb | (high << inv_cnt);
        low_limb = high >> cnt;
        rp = rp.offset(1);

        xs -= 1;
    }

    *rp = low_limb;

    return ret;
}
