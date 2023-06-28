use crate::{
    alloc::{AllocError, Allocator},
    reset_allocator::ResetAllocator,
};
use alloc_crate::alloc;
use core::{alloc::Layout, ptr::NonNull, sync::atomic::AtomicUsize};

/// [`LinearAllocator`] is an allocator that keeps a fixed-sized buffer internally
/// and use it to make allocations. Once the buffer is full, all next allocations fails.
///
/// This allocator is useful when you want a "scratch space" for multiple tiny allocations
/// that share the same lifetime.
///
/// # Usage:
/// ```
/// #![cfg_attr(not(feature = "stable"), feature(allocator_api))]
/// #[cfg(feature = "vec")]
/// {
///     use core::mem::size_of;
///
///     use piece::vec::Vec;
///     use piece::LinearAllocator;
///
///     let linear_allocator = LinearAllocator::with_capacity(64 * size_of::<i32>());
///
///     let mut vec1 = Vec::with_capacity_in(32, &linear_allocator);
///     let mut vec2 = Vec::with_capacity_in(32, &linear_allocator);
///
///     vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
///     vec2.extend_from_slice(&[6, 7, 8, 9, 10]);
///
///     assert_eq!(vec1, &[1, 2, 3, 4, 5]);
///     assert_eq!(vec2, &[6, 7, 8, 9, 10]);
/// }
/// ```
pub struct LinearAllocator {
    buf: NonNull<u8>,
    len: AtomicUsize,
    capacity: usize,
}

unsafe impl Allocator for LinearAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        use core::sync::atomic::Ordering;

        loop {
            let len = self.len.load(Ordering::Acquire);

            let padding = (layout.align() - ((self.buf.as_ptr() as usize + len) % layout.align()))
                % layout.align();

            let start_offset = len + padding;
            let new_len = start_offset + layout.size();

            if self.capacity < new_len {
                return Err(AllocError);
            }

            if self
                .len
                .compare_exchange(len, new_len, Ordering::Release, Ordering::Relaxed)
                .is_err()
            {
                continue;
            };

            // SAFETY: indexing inside the already allocated buffer
            let buf_ptr = unsafe { self.buf.as_ptr().add(start_offset) };

            // SAFETY: buf_ptr points to a slice reference, it can't be null
            let slice_ptr = unsafe {
                NonNull::slice_from_raw_parts(NonNull::new_unchecked(buf_ptr), layout.size())
            };

            return Ok(slice_ptr);
        }
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

impl Drop for LinearAllocator {
    fn drop(&mut self) {
        // SAFETY: buf pointer was allocated with std::alloc::alloc with the same layout
        unsafe {
            alloc::dealloc(
                self.buf.as_ptr(),
                Layout::array::<u8>(self.capacity).unwrap(),
            );
        }
    }
}

impl ResetAllocator for LinearAllocator {
    fn reset(&mut self) {
        *self.len.get_mut() = 0;
    }
}

unsafe impl Sync for LinearAllocator {}
unsafe impl Send for LinearAllocator {}

impl LinearAllocator {
    /// Creates a new LinearAllocator with the specified `capacity`
    ///
    /// PANIC:
    /// `capacity` must be greater than zero
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(capacity > 0);
        // SAFETY: the assertion above ensures that layout size is greater than zero
        let mem_ptr = unsafe { alloc::alloc(Layout::array::<u8>(capacity).unwrap()) };
        let mem_ptr = NonNull::new(mem_ptr).unwrap();

        Self {
            len: AtomicUsize::new(0),
            buf: mem_ptr,
            capacity,
        }
    }

    pub fn allocated_bytes(&self) -> usize {
        self.len.load(core::sync::atomic::Ordering::Relaxed)
    }
}
