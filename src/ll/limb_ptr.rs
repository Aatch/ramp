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

use std::{fmt, ops};
#[cfg(debug_assertions)]
use std::mem;
use std::cmp::Ordering;


/// A version of `*const Limb` that is bounds-checked when debug assertions are on
#[derive(Copy, Clone, Debug)]
#[allow(raw_pointer_derive)]
pub struct Limbs {
    ptr: *const Limb,
    bounds: Bounds,
}

/// A version of `*mut Limb` that is bounds-checked when debug assertions are on
#[derive(Copy, Clone)]
#[allow(raw_pointer_derive)]
pub struct LimbsMut {
    ptr: *mut Limb,
    bounds: Bounds,
}

macro_rules! api {
    ($ty: ident, $ptr: ty) => {
        impl $ty {
            /// Create a new instance, pointing at `base` and valid
            /// from `base.offset(start)` to `base.offset(end)`.
            pub unsafe fn new(base: $ptr, start: i32, end: i32) -> $ty {
                $ty {
                    ptr: base,
                    bounds: Bounds::new(base as usize, start, end)
                }
            }

            /// Move `self` to point to the `x`th Limbs from the
            /// current location.
            #[inline]
            pub unsafe fn offset(self, x: isize) -> $ty {
                debug_assert!(self.bounds.offset_valid(self.ptr as usize, x),
                              "invalid offset of {:?} by {}, which should be in {:?}", self.ptr, x, self.bounds);
                $ty {
                    ptr: self.ptr.offset(x),
                    bounds: self.bounds,
                }
            }
        }

        impl PartialEq for $ty {
            fn eq(&self, other: &$ty) -> bool {
                self.ptr == other.ptr
            }
        }
        impl PartialOrd for $ty {
            fn partial_cmp(&self, other: &$ty) -> Option<Ordering> {
                self.ptr.partial_cmp(&other.ptr)
            }
        }
        impl Eq for $ty {}
        impl Ord for $ty {
            fn cmp(&self, other: &$ty) -> Ordering {
                self.ptr.cmp(&other.ptr)
            }
        }

        impl ops::Deref for $ty {
            type Target = Limb;
            fn deref(&self) -> &Limb {
                debug_assert!(self.bounds.can_deref(self.ptr as usize),
                              "invalid deref of {:?}, which should be in {:?}", self.ptr, self.bounds);
                unsafe { &*self.ptr }
            }
        }
    }
}

api!(Limbs, *const Limb);
api!(LimbsMut, *mut Limb);
impl LimbsMut {
    /// View the `LimbsMut` as a `Limbs` (an explicit `*const
    /// Limb` -> `*mut Limb` conversion)
    pub fn as_const(self) -> Limbs {
        Limbs {
            ptr: self.ptr,
            bounds: self.bounds,
        }
    }
}
impl ops::DerefMut for LimbsMut {
    fn deref_mut(&mut self) -> &mut Limb {
        debug_assert!(self.bounds.can_deref(self.ptr as usize),
                      "invalid mut deref of {:?}, which should be in {:?}", self.ptr, self.bounds);
        unsafe { &mut *self.ptr }
    }
}

// This is where the magic is at: the bounds are only stored/checked
// in debug mode; release mode just powers ahead without any overhead.

#[derive(Copy, Clone)]
#[cfg(debug_assertions)]
struct Bounds {
    lo: usize,
    hi: usize,
}
#[derive(Copy, Clone)]
#[cfg(not(debug_assertions))]
struct Bounds;

#[cfg(debug_assertions)]
impl Bounds {
    fn new(ptr: usize, start: i32, end: i32) -> Bounds {
        assert!(start <= end);
        Bounds {
            lo: ptr + start as usize * mem::size_of::<Limb>(),
            hi: ptr + end as usize * mem::size_of::<Limb>(),
        }
    }
    fn can_deref(self, ptr: usize) -> bool {
        // a deref can't deref when we're at the limit
        self.lo <= ptr && ptr < self.hi
    }
    fn offset_valid(self, ptr: usize, offset: isize) -> bool {
        let bytes = offset * mem::size_of::<Limb>() as isize;
        let new = ptr.wrapping_add(bytes as usize);
        // an offset can point to the limit (i.e. one byte past the end)
        self.lo <= new && new <= self.hi
    }
}
#[cfg(not(debug_assertions))]
impl Bounds {
    fn new(_ptr: usize, _start: i32, _end: i32) -> Bounds { Bounds }
    #[inline]
    fn can_deref(self, _ptr: usize) -> bool { true }
    #[inline]
    fn offset_valid(self, _ptr: usize, _offset: isize) -> bool { true }
}
impl fmt::Debug for Bounds {
    #[cfg(debug_assertions)]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Bounds {{ lo: 0x{:x}, hi: 0x{:x} }}", self.lo, self.hi)
    }
    #[cfg(not(debug_assertions))]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Bounds {{ <optimised out> }}")
    }
}
