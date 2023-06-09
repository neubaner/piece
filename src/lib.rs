#![feature(allocator_api)]

use std::{
    alloc::{AllocError, Allocator},
    sync::Mutex,
};

// FIXME(neubaner): since a `Vec<T>` data pointer is not stable, it breaks this rule of `Allocator`;
//   - any pointer to a memory block which is currently allocated may be passed to any other method of the allocator.
// dumb me :p
struct Inner {
    memory: Vec<u8>,
    free_blocks: Vec<(usize, usize)>,
}

pub struct ArenaAllocator {
    inner: Mutex<Inner>,
}

unsafe impl Allocator for ArenaAllocator {
    fn allocate(
        &self,
        layout: std::alloc::Layout,
    ) -> Result<std::ptr::NonNull<[u8]>, std::alloc::AllocError> {
        let mut lock = self.inner.lock().unwrap();

        let memory_ptr = lock.memory.as_mut_ptr();
        let padding = (layout.align() - (memory_ptr as usize) % layout.align()) % layout.align(); // wtf...

        let free_block_index = lock.free_blocks.iter().position(|(_, size)| {
            let new_size = size - padding;
            layout.size() <= new_size
        });

        // TODO(neubaner): split blocks if required size is small
        if let Some(index) = free_block_index {
            let (offset, size) = lock.free_blocks.swap_remove(index);
            let offset = offset + padding;
            let size = size - padding;

            let reused_slice =
                core::ptr::slice_from_raw_parts_mut(unsafe { memory_ptr.add(offset) }, size);

            return Ok(unsafe { std::ptr::NonNull::new_unchecked(reused_slice) });
        }

        lock.memory
            .try_reserve(padding + layout.size())
            .map_err(|_| AllocError)?;

        let pre_len = lock.memory.len();

        let spare_slice = core::ptr::slice_from_raw_parts_mut(
            unsafe { memory_ptr.add(pre_len + padding) },
            layout.size(),
        );

        unsafe { lock.memory.set_len(pre_len + padding + layout.size()) };

        Ok(unsafe { std::ptr::NonNull::new_unchecked(spare_slice) })
    }

    unsafe fn deallocate(&self, ptr: std::ptr::NonNull<u8>, layout: std::alloc::Layout) {
        let mut lock = self.inner.lock().unwrap();

        let memory_ptr = lock.memory.as_ptr();
        let ptr = ptr.as_ptr();

        debug_assert!(memory_ptr <= ptr);

        lock.free_blocks
            .push(((ptr.offset_from(memory_ptr) as usize), layout.size()));
    }
}

impl ArenaAllocator {
    #[inline]
    pub const fn new() -> Self {
        Self {
            inner: Mutex::new(Inner {
                memory: Vec::new(),
                free_blocks: Vec::new(),
            }),
        }
    }

    #[inline]
    pub fn with_initial_capacity(capacity: usize) -> Self {
        Self {
            inner: Mutex::new(Inner {
                memory: Vec::with_capacity(capacity),
                free_blocks: Vec::new(),
            }),
        }
    }
}

#[cfg(test)]
mod test {
    use std::mem;

    use super::ArenaAllocator;

    #[test]
    fn should_keep_allocation_for_the_lifetime() {
        let arena_allocator = ArenaAllocator::with_initial_capacity(1024);

        let mut vec1 = Vec::with_capacity_in(32, &arena_allocator);
        let mut vec2 = Vec::with_capacity_in(32, &arena_allocator);
        let mut zero_sized_vec = Vec::new_in(&arena_allocator);

        vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
        vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

        zero_sized_vec.push(());
        zero_sized_vec.push(());
        zero_sized_vec.push(());

        assert_eq!(vec1, &[1, 2, 3, 4, 5]);
        assert_eq!(vec2, &[6, 7, 8, 9, 10]);
        assert_eq!(zero_sized_vec.len(), 3);

        assert_eq!(
            arena_allocator.inner.lock().unwrap().memory.len(),
            64 * mem::size_of::<i32>()
        );
    }

    #[test]
    fn should_reuse_block() {
        let arena_allocator = ArenaAllocator::with_initial_capacity(1024);
        let vec1: Vec<i32, _> = Vec::with_capacity_in(512, &arena_allocator);

        drop(vec1);
        assert_eq!(arena_allocator.inner.lock().unwrap().free_blocks.len(), 1);

        let vec2: Vec<i32, _> = Vec::with_capacity_in(256, &arena_allocator);
        assert_eq!(arena_allocator.inner.lock().unwrap().free_blocks.len(), 0);
        drop(vec2);

        assert_eq!(arena_allocator.inner.lock().unwrap().free_blocks.len(), 1);
    }
}
