#![deny(missing_docs)]
//! Mockalloc is a crate to allow testing code which uses the global allocator. It
//! uses a probabilistic algorithm to detect and distinguish several kinds of
//! allocation related bugs:
//!
//! - Memory leaks
//! - Double frees
//! - Invalid frees (bad pointer)
//! - Invalid frees (bad size)
//! - Invalid frees (bad alignment)
//!
//! ## Usage
//!
//! Typical use involves enabling the `Mockalloc` allocator during tests, eg:
//!
//! ```rust
//! #[cfg(test)]
//! mod tests {
//!     use std::alloc::System;
//!     use mockalloc::Mockalloc;
//!
//!     #[global_allocator]
//!     static ALLOCATOR: Mockalloc<System> = Mockalloc(System);
//! }
//! ```
//!
//! Once the allocator is enabled, there are several ways to use it in your tests.
//!
//! The easiest way is to use the `#[mockalloc::test]` attribute on your tests
//! instead of the usual `#[test]` attribute:
//!
//! ```rust
//!     #[mockalloc::test]
//!     fn it_works() {
//!         // Some code which uses the allocator
//!     }
//! ```
//!
//! The test will fail if any of the allocation bugs listed above are detected.
//! The test will also fail with the `NoData` error if no allocations are detected
//! so that you can be sure that the `Mockalloc` allocator is active.
//!
//! You can also use `mockalloc` to test a specific section of code for memory
//! issues without checking the entire test using the `assert_allocs` function.
//!
//! The `#[mockalloc::test]` attribute in the prior example is simply a shorthand
//! for:
//!
//! ```rust
//!     #[test]
//!     fn it_works() {
//!         mockalloc::assert_allocs(|| {
//!             // Some code which uses the allocator
//!         });
//!     }
//! ```
//!
//! It is also possible to make more detailed assertions: for example you may want
//! to assert that a piece of code performs a specific number of allocations. For
//! this you can use the `record_allocs` function:
//!
//! ```rust
//!     #[test]
//!     fn it_works() {
//!         let alloc_info = mockalloc::record_allocs(|| {
//!             // Some code which uses the allocator
//!         });
//!
//!         assert_eq!(alloc_info.num_allocs(), 2);
//!
//!         // This is what `assert_allocs` does internally:
//!         alloc_info.result().unwrap()
//!     }
//! ```
//!
//! ## Limitations
//!
//! Allocations are tracked separately for each thread. This allows tests to be
//! run in parallel, but it means that the library will report false positives
//! if a pointer returned by an allocation on one thread is later freed by a
//! different thread.
//!
//! The algorithm cannot detect where the bug is, it can only indicate what
//! kind of bug is present.
//!
//! ## How it works
//!
//! The allocator does its tracking without allocating any memory itself. It
//! uses a probabilistic algorithm which works by hashing various pieces of
//! metadata about allocations and frees, and then accumulating these using
//! a commutative operation so that the order does not affect the result.
//!
//! Depending on which of these accumulators returns to zero by the end of
//! a region under test, different allocation bugs can be distinguished.
//!
//! The following metadata is hashed and accumulated:
//!
//! - Pointer
//! - Size & Pointer
//! - Alignment & Pointer
//!
//! In addition to tracking the total number of allocations and frees.
//!
//! We can detect memory leaks and double frees by looking for a difference
//! between the total numbers of allocations and frees.
//!
//! Otherwise, if the pointer accumulator does not return to zero, we know that
//! an invalid pointer was freed.
//!
//! Otherwise, we know the right pointers were freed, but maybe with the wrong
//! size and/or alignment, which we can detect with the other two accumulators.
//!
//! If all accumulators returned to zero then we know everything is good.
//!
//! Each accumulator and hash is 128 bits to essentially eliminate the chance
//! of a collision.

use std::alloc::{GlobalAlloc, Layout};
use std::cell::RefCell;
use std::thread_local;

// Probably overkill, but performance isn't a huge concern
fn hash_fn(p: usize) -> u128 {
    const PRIME1: u128 = 257343791756393576901679996513787191589;
    const PRIME2: u128 = 271053192961985756828288246809453504189;
    let mut p = (p as u128).wrapping_add(PRIME2);
    p = p.wrapping_mul(PRIME1);
    p = p ^ (p >> 64);
    p = p.wrapping_mul(PRIME2);
    p = p ^ (p >> 42);
    p = p.wrapping_mul(PRIME1);
    p = p ^ (p >> 25);
    p
}

#[derive(Default)]
struct LocalState {
    enabled: bool,
    ptr_accum: u128,
    ptr_size_accum: u128,
    ptr_align_accum: u128,
    num_allocs: u64,
    num_frees: u64,
}

impl LocalState {
    fn record_alloc(&mut self, ptr: *const u8, layout: Layout) {
        if !self.enabled || ptr.is_null() {
            return;
        }
        let ptr_hash = hash_fn(ptr as usize);
        let size_hash = hash_fn(layout.size());
        let align_hash = hash_fn(layout.align());
        self.ptr_accum = self.ptr_accum.wrapping_add(ptr_hash);
        self.ptr_size_accum = self
            .ptr_size_accum
            .wrapping_add(ptr_hash.wrapping_mul(size_hash));
        self.ptr_align_accum = self
            .ptr_align_accum
            .wrapping_add(ptr_hash.wrapping_mul(align_hash));
        self.num_allocs += 1;
    }
    fn record_free(&mut self, ptr: *const u8, layout: Layout) {
        if !self.enabled {
            return;
        }
        let ptr_hash = hash_fn(ptr as usize);
        let size_hash = hash_fn(layout.size());
        let align_hash = hash_fn(layout.align());
        self.ptr_accum = self.ptr_accum.wrapping_sub(ptr_hash);
        self.ptr_size_accum = self
            .ptr_size_accum
            .wrapping_sub(ptr_hash.wrapping_mul(size_hash));
        self.ptr_align_accum = self
            .ptr_align_accum
            .wrapping_sub(ptr_hash.wrapping_mul(align_hash));
        self.num_frees += 1;
    }
    fn start(&mut self) {
        assert!(!self.enabled, "Mockalloc already enabled");
        self.enabled = true;
        self.ptr_accum = 0;
        self.ptr_size_accum = 0;
        self.ptr_align_accum = 0;
        self.num_allocs = 0;
        self.num_frees = 0;
    }

    fn finish(&mut self) -> AllocInfo {
        self.enabled = false;
        let result = if self.num_allocs > self.num_frees {
            Err(AllocError::Leak)
        } else if self.num_allocs < self.num_frees {
            Err(AllocError::DoubleFree)
        } else if self.num_allocs == 0 {
            Err(AllocError::NoData)
        } else if self.ptr_accum != 0 {
            Err(AllocError::BadPtr)
        } else {
            match (self.ptr_size_accum != 0, self.ptr_align_accum != 0) {
                (true, true) => Err(AllocError::BadLayout),
                (true, false) => Err(AllocError::BadSize),
                (false, true) => Err(AllocError::BadAlignment),
                (false, false) => Ok(()),
            }
        };
        AllocInfo {
            result,
            num_allocs: self.num_allocs,
            num_frees: self.num_frees,
        }
    }
}

thread_local! {
    static LOCAL_STATE: RefCell<LocalState> = RefCell::new(LocalState::default());
}

/// Wraps an existing allocator to allow detecting allocation bugs.
/// You should use the `#[global_allocator]` attribute to activate
/// this allocator.
pub struct Mockalloc<T: GlobalAlloc>(pub T);

unsafe impl<T: GlobalAlloc> GlobalAlloc for Mockalloc<T> {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        let ptr = self.0.alloc(layout);
        LOCAL_STATE.with(|rc| {
            let mut state = rc.borrow_mut();
            state.record_alloc(ptr, layout);
        });
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        LOCAL_STATE.with(|rc| {
            let mut state = rc.borrow_mut();
            state.record_free(ptr, layout);
        });
        self.0.dealloc(ptr, layout);
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // SAFETY: the caller must ensure that the `new_size` does not overflow.
        // `layout.align()` comes from a `Layout` and is thus guaranteed to be valid.
        let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
        let new_ptr = self.0.realloc(ptr, layout, new_size);
        LOCAL_STATE.with(|rc| {
            let mut state = rc.borrow_mut();
            state.record_free(ptr, layout);
            state.record_alloc(new_ptr, new_layout);
        });
        new_ptr
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let ptr = self.0.alloc_zeroed(layout);
        LOCAL_STATE.with(|rc| {
            let mut state = rc.borrow_mut();
            state.record_alloc(ptr, layout);
        });
        ptr
    }
}

/// Types of allocation bug which can be detected by the allocator.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum AllocError {
    /// No allocations were detected. Perhaps `Mockalloc` isn't enabled
    /// as the global allocator?
    NoData,
    /// There were more calls to `alloc` than to `dealloc`.
    Leak,
    /// There were more calls to `dealloc` than to `alloc`.
    DoubleFree,
    /// A pointer was passed to `dealloc` which was not previously
    /// returned by `alloc`.
    BadPtr,
    /// The size specified in a call to `dealloc` did not match that
    /// specified in the corresponding `alloc` call.
    BadSize,
    /// The alignment specified in a call to `dealloc` did not match that
    /// specified in the corresponding `alloc` call.
    BadAlignment,
    /// The size and alignment specified in a call to `dealloc` did not match
    /// those specified in the corresponding `alloc` call.
    BadLayout,
}

/// Captures information about the allocations performed by a region under
/// test.
#[derive(Debug, Clone)]
pub struct AllocInfo {
    num_allocs: u64,
    num_frees: u64,
    result: Result<(), AllocError>,
}

impl AllocInfo {
    /// Returns the total number of allocations performed.
    pub fn num_allocs(&self) -> u64 {
        self.num_allocs
    }
    /// Returns the total number of frees performed.
    pub fn num_frees(&self) -> u64 {
        self.num_frees
    }
    /// Returns an `Err(..)` result if any allocation bugs were detected.
    pub fn result(&self) -> Result<(), AllocError> {
        self.result.clone()
    }
}

struct AllocChecker(bool);

impl AllocChecker {
    fn new() -> Self {
        LOCAL_STATE.with(|rc| rc.borrow_mut().start());
        Self(true)
    }
    fn finish(mut self) -> AllocInfo {
        self.0 = false;
        LOCAL_STATE.with(|rc| rc.borrow_mut().finish())
    }
}

impl Drop for AllocChecker {
    fn drop(&mut self) {
        if self.0 {
            LOCAL_STATE.with(|rc| rc.borrow_mut().finish());
        }
    }
}

/// Records the allocations within a code block.
pub fn record_allocs(f: impl FnOnce()) -> AllocInfo {
    let checker = AllocChecker::new();
    f();
    checker.finish()
}

/// Records the allocations within a code block and asserts that no issues
/// were detected.
///
/// No checks are performed if `miri` is detected, as we cannot collect
/// allocation data in that case, and `miri` performs many of these
/// checks already.
pub fn assert_allocs(f: impl FnOnce()) {
    if cfg!(miri) {
        f();
    } else {
        record_allocs(f).result.unwrap();
    }
}

/// Returns `true` if allocations are currently being recorded, ie. if
/// we're inside a call to `record_allocs`.
pub fn is_recording() -> bool {
    LOCAL_STATE.with(|rc| rc.borrow().enabled)
}

pub use mockalloc_macros::test;

#[cfg(test)]
mod tests {
    use super::{is_recording, record_allocs, AllocError, Mockalloc};
    use std::alloc::{GlobalAlloc, Layout, System};
    use std::{cmp, mem, ptr};

    struct LeakingAllocator(System);

    unsafe impl GlobalAlloc for LeakingAllocator {
        unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
            self.0.alloc_zeroed(layout)
        }

        unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
            if is_recording() {
                // SAFETY: the caller must ensure that the `new_size` does not overflow.
                // `layout.align()` comes from a `Layout` and is thus guaranteed to be valid.
                let new_layout = Layout::from_size_align_unchecked(new_size, layout.align());
                // SAFETY: the caller must ensure that `new_layout` is greater than zero.
                let new_ptr = self.alloc(new_layout);
                if !new_ptr.is_null() {
                    // SAFETY: the previously allocated block cannot overlap the newly allocated block.
                    // The safety contract for `dealloc` must be upheld by the caller.
                    ptr::copy_nonoverlapping(ptr, new_ptr, cmp::min(layout.size(), new_size));
                    self.dealloc(ptr, layout);
                }
                new_ptr
            } else {
                self.0.realloc(ptr, layout, new_size)
            }
        }

        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            self.0.alloc(layout)
        }

        unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
            if !is_recording() {
                self.0.dealloc(ptr, layout);
            }
        }
    }

    // We suppress calls to `dealloc` whilst recording so that our tests don't cause UB
    // when simulating bad requests to the allocator.
    #[global_allocator]
    static A: Mockalloc<LeakingAllocator> = Mockalloc(LeakingAllocator(System));

    fn do_some_allocations() -> Vec<Box<i32>> {
        let mut a = Vec::new();
        let mut b = Vec::new();
        for i in 0..32 {
            let p = Box::new(i);
            if i % 2 == 0 {
                a.push(p);
            } else {
                b.push(p);
            }
        }
        a
    }

    #[test]
    fn it_works() {
        let alloc_info = record_allocs(|| {
            let _p = Box::new(42);
        });
        alloc_info.result().unwrap();
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 1);
    }

    #[test]
    fn it_detects_leak() {
        let alloc_info = record_allocs(|| {
            mem::forget(Box::new(42));
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::Leak);
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 0);
    }

    #[test]
    fn it_detects_bad_layout() {
        let alloc_info = record_allocs(|| unsafe {
            mem::transmute::<_, Box<f64>>(Box::new(42u32));
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadLayout);
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 1);
    }

    #[test]
    fn it_detects_no_data() {
        let alloc_info = record_allocs(|| ());
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::NoData);
        assert_eq!(alloc_info.num_allocs, 0);
        assert_eq!(alloc_info.num_frees, 0);
    }

    #[test]
    fn it_detects_bad_alignment() {
        let alloc_info = record_allocs(|| unsafe {
            mem::transmute::<_, Box<[u8; 4]>>(Box::new(42u32));
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadAlignment);
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 1);
    }

    #[test]
    fn it_detects_bad_size() {
        let alloc_info = record_allocs(|| unsafe {
            mem::transmute::<_, Box<[u32; 2]>>(Box::new(42u32));
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadSize);
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 1);
    }

    #[test]
    fn it_detects_double_free() {
        let alloc_info = record_allocs(|| unsafe {
            let mut x = mem::ManuallyDrop::new(Box::new(42));
            mem::ManuallyDrop::drop(&mut x);
            mem::ManuallyDrop::drop(&mut x);
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::DoubleFree);
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 2);
    }

    #[test]
    fn it_detects_bad_ptr() {
        let alloc_info = record_allocs(|| unsafe {
            let mut x = Box::new(42);
            *mem::transmute::<_, &mut usize>(&mut x) += 1;
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadPtr);
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 1);
    }

    #[test]
    fn it_works_amongst_many() {
        let alloc_info = record_allocs(|| {
            let _unused = do_some_allocations();
            let _p = Box::new(42);
            let _unused = do_some_allocations();
        });
        alloc_info.result().unwrap();
    }

    #[test]
    fn it_detects_leak_amongst_many() {
        let alloc_info = record_allocs(|| {
            let _unused = do_some_allocations();
            let p = Box::new(42);
            let _unused = do_some_allocations();
            mem::forget(p);
            let _unused = do_some_allocations();
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::Leak);
    }

    #[test]
    fn it_detects_bad_layout_amongst_many() {
        let alloc_info = record_allocs(|| unsafe {
            let _unused = do_some_allocations();
            let p = Box::new(42u32);
            let _unused = do_some_allocations();
            mem::transmute::<_, Box<f64>>(p);
            let _unused = do_some_allocations();
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadLayout);
    }

    #[test]
    fn it_detects_bad_alignment_amongst_many() {
        let alloc_info = record_allocs(|| unsafe {
            let _unused = do_some_allocations();
            let p = Box::new(42u32);
            let _unused = do_some_allocations();
            mem::transmute::<_, Box<[u8; 4]>>(p);
            let _unused = do_some_allocations();
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadAlignment);
    }

    #[test]
    fn it_detects_bad_size_amongst_many() {
        let alloc_info = record_allocs(|| unsafe {
            let _unused = do_some_allocations();
            let p = Box::new(42u32);
            let _unused = do_some_allocations();
            mem::transmute::<_, Box<[u32; 2]>>(p);
            let _unused = do_some_allocations();
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadSize);
    }

    #[test]
    fn it_detects_double_free_amongst_many() {
        let alloc_info = record_allocs(|| unsafe {
            let _unused = do_some_allocations();
            let mut x = mem::ManuallyDrop::new(Box::new(42));
            let _unused = do_some_allocations();
            mem::ManuallyDrop::drop(&mut x);
            let _unused = do_some_allocations();
            mem::ManuallyDrop::drop(&mut x);
            let _unused = do_some_allocations();
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::DoubleFree);
    }

    #[test]
    fn it_detects_bad_ptr_amongst_many() {
        let alloc_info = record_allocs(|| unsafe {
            let _unused = do_some_allocations();
            let mut x = Box::new(42);
            let _unused = do_some_allocations();
            *mem::transmute::<_, &mut usize>(&mut x) += 1;
            let _unused = do_some_allocations();
        });
        assert_eq!(alloc_info.result().unwrap_err(), AllocError::BadPtr);
    }
}
