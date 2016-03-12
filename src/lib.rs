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

#![crate_type="lib"]
#![crate_name="ramp"]

#![feature(core_intrinsics, asm, heap_api, associated_consts)]
#![feature(zero_one, step_trait, unique, alloc)]

#![cfg_attr(test, feature(test))]

#[cfg(test)] extern crate test;

extern crate alloc;
extern crate rand;
extern crate hamming;

pub mod ll;
mod mem;

pub mod int;

// Re-exports

pub use int::Int;
pub use int::RandomInt;
