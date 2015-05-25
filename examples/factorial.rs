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

extern crate ramp;

use ramp::Int;

fn main() {
    println!("5!: {}", factorial(5));
    println!("10!: {}", factorial(10));
    println!("20!: {}", factorial(20));
    println!("100!: {}", factorial(100));
    println!("1000!: {}", factorial(1000));
    println!("20000!: {}", factorial(20000));
}

/// Calculates n!
fn factorial(n: usize) -> Int {
    let mut a = Int::from(1);
    if n == 0 || n == 1 {
        return a;
    }

    for i in 2..n {
        a = a * i;
    }

    return a * n;
}
