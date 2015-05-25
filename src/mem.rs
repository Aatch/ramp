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

//! Memory management functions. The base functions align to a pointer-width, so they shouldn't
//! be used for anything that requires an alignment greater than that.

use std::rt::heap;
use std::mem;
use std::intrinsics::abort;
use std::io::{self, Write};
use std::ptr;

pub unsafe fn allocate_bytes(size: usize) -> *mut u8 {
    let ret = heap::allocate(size, mem::align_of::<usize>());
    if ret.is_null() {
        let _ = writeln!(io::stderr(), "Failed to allocate memory (size={})", size);
        abort();
    }
    ret
}

pub unsafe fn allocate<T>(n: usize) -> *mut T {
    allocate_bytes(n * mem::size_of::<T>()) as *mut T
}

pub unsafe fn reallocate(old: *mut u8, old_size: usize, new_size: usize) -> *mut u8 {
    let ret = heap::reallocate(old, old_size, new_size, mem::align_of::<usize>());
    if ret.is_null() {
        let _ = writeln!(io::stderr(), "Failed to reallocate memory (old size={}, new size={})",
                         old_size, new_size);
        abort();
    }
    ret
}

pub unsafe fn deallocate(ptr: *mut u8, size: usize) {
    heap::deallocate(ptr, size, mem::align_of::<usize>());
}

/// Allocate for temporary storage. Ensures that the allocations are
/// freed when the structure drops
pub struct TmpAllocator {
    mark: *mut Marker
}

struct Marker {
    next: *mut Marker,
    size: usize
}

impl TmpAllocator {
    pub fn new() -> TmpAllocator {
        TmpAllocator {
            mark: ptr::null_mut()
        }
    }

    pub unsafe fn allocate_bytes(&mut self, size: usize) -> *mut u8 {
        let total_size = size + mem::size_of::<Marker>();
        let ptr = allocate_bytes(size);

        let mark = ptr as *mut Marker;
        (*mark).size = total_size;
        (*mark).next = self.mark;

        self.mark = mark;

        ptr.offset(mem::size_of::<Marker>() as isize)
    }

    /// Allocate space for n instances of `T`
    pub unsafe fn allocate<T>(&mut self, n: usize) -> *mut T {
        self.allocate_bytes(n * mem::size_of::<T>()) as *mut T
    }

    /// Allocates space for n1+n2 instances of `T` and returns a pair of pointers.
    pub unsafe fn allocate_2<T>(&mut self, n1: usize, n2: usize) -> (*mut T, *mut T) {
        let x = self.allocate(n1 + n2);
        let y = x.offset(n1 as isize);
        (x, y)
    }
}

impl Drop for TmpAllocator {
    fn drop(&mut self) {
        unsafe {
            let mut next;
            let mut mark = self.mark;
            while !mark.is_null() {
                next = (*mark).next;
                let size = (*mark).size;
                deallocate(mark as *mut u8, size);
                mark = next;
            }
        }
    }
}
