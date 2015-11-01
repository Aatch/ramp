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

/*!
 * Traits for performing an operation and reusing and existing allocation.
 *
 * These allow for reuse of the space already allocated for other numbers.
 * Primarily aimed at improving the efficiency when using temporary variables
 * like so:
 *
 * ```ignore
 *     t = &a * &b
 * ```
 *
 * Will allocate a new Int for the result and destroy the value already in `t`.
 * Instead, these traits allow you to write:
 *
 * ```ignore
 *    t.add_into(&a, &b)
 * ```
 *
 * Which will attempt to re-use the allocation in `t`.
 */

pub trait AddInto<L,R> {
    fn add_into(&mut self, l: L, r: R);
}

pub trait SubInto<L,R> {
    fn sub_into(&mut self, l: L, r: R);
}

pub trait MulInto<L,R> {
    fn mul_into(&mut self, l: L, r: R);
}

pub trait DivInto<L,R> {
    fn div_into(&mut self, l: L, r: R);
}

pub trait RemInto<L,R> {
    fn rem_into(&mut self, l: L, r: R);
}

pub trait ShlInto<L,R> {
    fn shl_into(&mut self, l: L, r: R);
}

pub trait ShrInto<L,R> {
    fn shr_into(&mut self, l: L, r: R);
}

pub trait BitAndInto<L,R> {
    fn bitand_into(&mut self, l: L, r: R);
}

pub trait BitOrInto<L,R> {
    fn bitor_into(&mut self, l: L, r: R);
}

pub trait BitXorInto<L,R> {
    fn bitxor_into(&mut self, l: L, r: R);
}
