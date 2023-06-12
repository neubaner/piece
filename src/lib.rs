#![feature(allocator_api)]

mod linear_allocator;

#[macro_use]
extern crate static_assertions;

use crate::linear_allocator::LinearAllocator;
use std::{
    alloc::{AllocError, Allocator, Layout},
    cell::Cell,
    ptr::NonNull,
};

type BlockCell<const SIZE: usize> = Cell<Option<NonNull<LinearAllocator<SIZE>>>>;

pub struct FallbackAllocator<const BLOCK_SIZE: usize> {
    next_free_block: BlockCell<BLOCK_SIZE>,
}

unsafe impl<const BLOCK_SIZE: usize> Allocator for FallbackAllocator<BLOCK_SIZE> {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        match self.next_free_block.get() {
            None => {
                let block = Box::try_new(LinearAllocator::<BLOCK_SIZE>::new())?;

                let buf_ptr = block.allocate(layout)?;

                // SAFETY: `Box::into_raw` always returns non-null pointer
                self.next_free_block.set(Some(unsafe {
                    NonNull::new_unchecked(Box::into_raw(block))
                }));

                return Ok(buf_ptr);
            }
            Some(_free_block) => Err(AllocError),
        }

        /* let mut lock = self.inner.lock().unwrap();

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

            return Ok(unsafe { NonNull::new_unchecked(reused_slice) });
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

        Ok(unsafe { NonNull::new_unchecked(spare_slice) }) */
    }

    unsafe fn deallocate(&self, _ptr: NonNull<u8>, _layout: Layout) {
        /* let mut lock = self.inner.lock().unwrap();

        let memory_ptr = lock.memory.as_ptr();
        let ptr = ptr.as_ptr();

        debug_assert!(memory_ptr <= ptr);

        lock.free_blocks
            .push(((ptr.offset_from(memory_ptr) as usize), layout.size())); */
    }
}

impl<const BLOCK_SIZE: usize> FallbackAllocator<BLOCK_SIZE> {
    #[inline]
    pub const fn new() -> Self {
        Self {
            next_free_block: Cell::new(None),
        }
    }
}
