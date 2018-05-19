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

use std::alloc::{Global, Layout, Alloc};
use std::mem;
use std::intrinsics::abort;
use std::io::{self, Write};
use std::ptr::{self, NonNull};

use ll::limb::Limb;
use ll::limb_ptr::LimbsMut;

/// Returns a Layout with the given size and pointer-width (i.e., usize) alignment. Panics if
/// unable to create the Layout.
unsafe fn get_usize_align_layout(size: usize) -> Layout {
    let alignment = mem::align_of::<usize>();

    if let Ok(l) = Layout::from_size_align(size, alignment) {
        l
    }
    else {
        writeln!(io::stderr(),
                 "Failed to construct mem layout (size={}, alignment={})",
                 size,
                 alignment).unwrap();
        abort();
    }
}

pub unsafe fn allocate_bytes(size: usize) -> *mut u8 {
    let layout = get_usize_align_layout(size);
    let ret = match Global.alloc(layout.clone()) {
        Ok(p) => p.cast::<u8>().as_ptr(),
        Err(e) => {
            writeln!(io::stderr(),
                     "Failed to allocate memory (layout={:?}).\nError: {:?}",
                     layout,
                     e).unwrap();
            abort();
        }
    };

    ptr::write_bytes(ret, 0, size);
    ret
}

pub unsafe fn deallocate_bytes(ptr: *mut u8, size: usize) {
    let layout = get_usize_align_layout(size);
    Global.dealloc(NonNull::new(ptr).unwrap().as_opaque(), layout);
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
        let size = size + mem::size_of::<Marker>();
        let ptr = allocate_bytes(size);

        let mark = ptr as *mut Marker;
        (*mark).size = size;
        (*mark).next = self.mark;

        self.mark = mark;

        ptr.offset(mem::size_of::<Marker>() as isize)
    }

    /// Allocate space for n limbs
    pub unsafe fn allocate(&mut self, n: usize) -> LimbsMut {
        let ptr = self.allocate_bytes(n * mem::size_of::<Limb>()) as *mut Limb;
        LimbsMut::new(ptr, 0, n as i32)
    }

    /// Allocates space for n1+n2 limbs and returns a pair of pointers.
    pub unsafe fn allocate_2(&mut self, n1: usize, n2: usize) -> (LimbsMut, LimbsMut) {
        let mut x = self.allocate(n1 + n2);
        let mut y = x.offset(n1 as isize);
        (LimbsMut::new(&mut *x, 0, n1 as i32),
         LimbsMut::new(&mut *y, 0, n2 as i32))
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
                deallocate_bytes(mark as *mut u8, size);
                mark = next;
            }
        }
    }
}
