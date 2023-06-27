#![cfg_attr(not(feature = "stable"), feature(allocator_api))]
#![cfg(feature = "vec")]

#[cfg(feature = "stable")]
use allocator_api2::alloc::{AllocError, Allocator, Global};

#[cfg(not(feature = "stable"))]
extern crate alloc;

#[cfg(not(feature = "stable"))]
use alloc::alloc::{AllocError, Allocator, Global};

use core::alloc::Layout;
use core::mem::size_of;
use core::ptr::NonNull;
use piece::{ChainAllocator, LinearAllocator};
use std::sync::Mutex;

#[test]
fn should_create_a_new_allocator_when_needed() {
    use piece::vec::Vec;

    // NOTE(gneubaner): each allocation has a pointer to the allocator used
    let chain_allocator = ChainAllocator::new(|| {
        LinearAllocator::with_capacity(32 * size_of::<i32>() + size_of::<*const ()>())
    });

    let mut vec1 = Vec::with_capacity_in(32, chain_allocator.by_ref());
    let mut vec2 = Vec::with_capacity_in(32, chain_allocator.by_ref());

    vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
    vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

    assert_eq!(vec1, &[1, 2, 3, 4, 5]);
    assert_eq!(vec2, &[6, 7, 8, 9, 10]);
    assert_eq!(2, chain_allocator.allocator_count());
}

#[test]
fn should_reuse_the_same_allocator() {
    use piece::vec::Vec;

    let chain_allocator =
        ChainAllocator::new(|| LinearAllocator::with_capacity(1024 * size_of::<i32>()));

    let mut vec1 = Vec::with_capacity_in(32, chain_allocator.by_ref());
    let mut vec2 = Vec::with_capacity_in(32, chain_allocator.by_ref());

    vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
    vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

    assert_eq!(vec1, &[1, 2, 3, 4, 5]);
    assert_eq!(vec2, &[6, 7, 8, 9, 10]);
    assert_eq!(1, chain_allocator.allocator_count());
}

#[test]
fn should_track_every_allocation() {
    use piece::vec::Vec;

    struct StubAllocator {
        vec: Mutex<Vec<NonNull<u8>>>,
    }

    unsafe impl Allocator for StubAllocator {
        fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
            let global = Global;
            let allocation = global.allocate(layout)?;

            self.vec.lock().unwrap().push(allocation.cast());

            Ok(allocation)
        }

        unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
            let global = Global;

            assert!(self.vec.lock().unwrap().contains(&ptr));

            global.deallocate(ptr, layout);
        }
    }

    impl Default for StubAllocator {
        fn default() -> Self {
            Self {
                vec: Mutex::new(Vec::new()),
            }
        }
    }

    let chain_allocator = ChainAllocator::new(|| StubAllocator::default());
    let mut vec1: Vec<i32, _> = Vec::with_capacity_in(32, chain_allocator.by_ref());
    let mut vec2: Vec<i32, _> = Vec::with_capacity_in(32, chain_allocator.by_ref());

    vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
    vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

    assert_eq!(vec1, &[1, 2, 3, 4, 5]);
    assert_eq!(vec2, &[6, 7, 8, 9, 10]);

    assert_eq!(1, chain_allocator.allocator_count());
}

#[test]
fn should_be_safe_to_send_across_threads() {
    use piece::vec::Vec;

    // NOTE(gneubaner): each allocation has a pointer to the allocator used
    let chain_allocator = ChainAllocator::new(|| {
        LinearAllocator::with_capacity(32 * size_of::<i32>() + size_of::<*const ()>())
    });

    let mut vec1 = Vec::with_capacity_in(32, chain_allocator.by_ref());
    vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
    assert_eq!(vec1, &[1, 2, 3, 4, 5]);
    assert_eq!(chain_allocator.allocator_count(), 1);
    drop(vec1);

    let handle = std::thread::spawn(move || {
        let mut vec2 = Vec::with_capacity_in(32, chain_allocator.by_ref());
        vec2.extend_from_slice(&[6, 7, 8, 9, 10]);
        assert_eq!(vec2, &[6, 7, 8, 9, 10]);
        assert_eq!(chain_allocator.allocator_count(), 2);
    });

    let _ = handle.join();
}
