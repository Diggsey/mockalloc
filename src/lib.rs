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
}

#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum AllocError {
    NoData,
    Leak,
    DoubleFree,
    BadPtr,
    BadSize,
    BadAlignment,
    BadLayout,
}

#[derive(Debug, Clone)]
pub struct AllocInfo {
    num_allocs: u64,
    num_frees: u64,
    result: Result<(), AllocError>,
}

impl AllocInfo {
    pub fn num_allocs(&self) -> u64 {
        self.num_allocs
    }
    pub fn num_frees(&self) -> u64 {
        self.num_frees
    }
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

pub fn record_allocs(f: impl FnOnce()) -> AllocInfo {
    let checker = AllocChecker::new();
    f();
    checker.finish()
}

pub fn assert_allocs(f: impl FnOnce()) {
    record_allocs(f).result.unwrap();
}

pub use mockalloc_macros::test;

#[cfg(test)]
mod tests {
    use super::{record_allocs, Mockalloc};
    use std::alloc::System;

    #[global_allocator]
    static A: Mockalloc<System> = Mockalloc(System);

    #[test]
    fn it_works() {
        let alloc_info = record_allocs(|| {
            let _p = Box::new(42);
        });
        alloc_info.result().unwrap();
        assert_eq!(alloc_info.num_allocs, 1);
        assert_eq!(alloc_info.num_frees, 1);
    }
}
