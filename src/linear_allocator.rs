use std::{
    alloc::{AllocError, Allocator, Layout},
    ptr::NonNull,
    sync::atomic::AtomicUsize,
};

pub struct LinearAllocator<const SIZE: usize> {
    buf: NonNull<u8>,
    len: AtomicUsize,
}

unsafe impl<const SIZE: usize> Allocator for LinearAllocator<SIZE> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        use std::sync::atomic::Ordering;

        loop {
            let len = self.len.load(Ordering::Acquire);

            let padding = (layout.align() - ((self.buf.as_ptr() as usize + len) % layout.align()))
                % layout.align();

            let new_len = len + padding + layout.size();

            if SIZE < new_len {
                return Err(AllocError);
            }

            if self
                .len
                .compare_exchange(len, new_len, Ordering::Release, Ordering::Relaxed)
                .is_err()
            {
                continue;
            };

            let buf_ptr = unsafe { self.buf.as_ptr().add(new_len) };

            break Ok(
                // SAFETY: buf_ptr points to a slice reference, it can't be null
                unsafe {
                    NonNull::slice_from_raw_parts(NonNull::new_unchecked(buf_ptr), layout.size())
                },
            );
        }
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {}
}

impl<const SIZE: usize> Drop for LinearAllocator<SIZE> {
    fn drop(&mut self) {
        unsafe { std::alloc::dealloc(self.buf.as_ptr(), Layout::array::<u8>(SIZE).unwrap()) };
    }
}

unsafe impl<const SIZE: usize> Sync for LinearAllocator<SIZE> {}
unsafe impl<const SIZE: usize> Send for LinearAllocator<SIZE> {}

impl<const SIZE: usize> LinearAllocator<SIZE> {
    pub fn new() -> Self {
        let mem_ptr = unsafe { std::alloc::alloc(Layout::array::<u8>(SIZE).unwrap()) };
        let mem_ptr = NonNull::new(mem_ptr).unwrap();

        Self {
            len: 0.into(),
            // SAFETY: It's safe to `assume_init` because the slice is a bunch of `MaybeUninit`
            buf: mem_ptr,
        }
    }
}

#[cfg(test)]
mod test {
    use std::mem::size_of;
    use std::sync::atomic::Ordering;

    use super::*;

    #[test]
    fn should_keep_allocation_for_the_lifetime() {
        let linear_allocator = LinearAllocator::<{ 1024 * size_of::<i32>() }>::new();

        let mut vec1 = Vec::with_capacity_in(32, &linear_allocator);
        let mut vec2 = Vec::with_capacity_in(32, &linear_allocator);
        let mut zero_sized_vec = Vec::new_in(&linear_allocator);

        vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
        vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

        zero_sized_vec.push(());
        zero_sized_vec.push(());
        zero_sized_vec.push(());

        assert_eq!(
            linear_allocator.len.load(Ordering::Relaxed),
            64 * size_of::<i32>()
        );
        assert_eq!(vec1, &[1, 2, 3, 4, 5]);
        assert_eq!(vec2, &[6, 7, 8, 9, 10]);
        assert_eq!(zero_sized_vec.len(), 3);
    }

    #[test]
    fn should_reuse_block() {
        let linear_allocator = LinearAllocator::<{ 1024 * size_of::<i32>() }>::new();
        let vec1: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);

        drop(vec1);

        let vec2: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);
        drop(vec2);

        assert_eq!(
            linear_allocator.len.load(Ordering::Relaxed),
            1024 * size_of::<i32>()
        );
    }

    #[test]
    fn linear_allocator_should_work_on_a_multithread_environment() {
        let linear_allocator = LinearAllocator::<{ 1024 * 1024 * 1024 }>::new();

        std::thread::scope(|s| {
            let linear_allocator = &linear_allocator;
            for i in 1..10000 {
                s.spawn(move || {
                    let mut vec: Vec<i32, _> = Vec::with_capacity_in(1024, linear_allocator);
                    let slice: Vec<i32> = (i..i + 1024).into_iter().collect();
                    vec.extend(slice.iter());

                    assert_eq!(vec, slice);
                });
            }
        })
    }
}
