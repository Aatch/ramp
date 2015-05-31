# RAMP - Rust Arithmetic in Multiple Precision

[![Build Status](https://travis-ci.org/Aatch/ramp.svg?branch=master)](https://travis-ci.org/Aatch/ramp)

Ramp is a high-performance mulitple-precision (aka "BigNum") library for working with numbers
bigger than can normally be handled. Usage is very easy, you can almost use them as regular
numbers.

## Example

```rust

extern crate ramp;
use ramp::Int;

// Calculates n!
fn factorial(n: usize) -> Int {
   let mut a = Int::from(1);

   for i in 2..n {
       a = a * i;
   }

   return a * n;
}
```

As you can see, it is very easy to work with these numbers.

Operator overloads have been provided for by-value, which consumes the operand(s) and by-reference,
which does not. The by-value overloads will attempt to re-use the space for the result (this isn't
always possible).

Operator overloads have also been provided for `i32` and `usize`, allowing easy (and efficient)
operations when you have smaller numbers. The above example actually uses the `usize` overload,
meaning only one `Int` is ever allocated.

**NOTE** Due to use of unstable features (notably inline assembly), Ramp can only be compiled with
a nightly build of `rustc`.

## Why another library?

The `num` crate provides some bignum types that can be used, why use Ramp instead? Well, Ramp is
much more focussed, `num` is a general-purpose numerics library that happens to provide some
multiple-precision arithmetic. Ramp is specifically focussed on multiple-precision arithmetic.

You should `num` if you aren't able to use unstable Rust features or just want a small amount of
functionality. Ramp should be used when you need high-performance and extra functionality.

## Overall Design

Ramp is split into two main parts: high-level code and low-level code. The high-level code is what
you should be using, however the low-level code is where the real work is done.

The low-level routines (in `ll`) are predominately unsafe functions that work with raw pointers,
some of the routines are implemented using inline assembly to gain access to processor-specific
functionality.

### Limbs

The term "Limb" is used frequently in Ramp. It's a term borrowed from GMP and is a single "digit"
for the base that Ramp works in. Since the base is equal to 2^word_size, these are very large
"digits", hence the use of the word "Limb" instead.

## Future Work

Ramp is currently very rough and incomplete. Broadly, there are three types Ramp aims to provide:
integers, rationals and floats. Integers (`Int`), is present, but incomplete, the other two are not
yet implemented.

In the low-level routines, there are a few operations, notably multiplication and division, that
are currently implemented using the simplest working algorithm. While this is sufficient for
relatively small numbers, larger numbers should be using better algorithms.