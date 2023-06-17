#![feature(allocator_api)]
#![warn(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::std_instead_of_core
)]

mod linear_allocator;

use std::{
    alloc::{AllocError, Allocator, Layout},
    cell::Cell,
    marker::PhantomData,
    ptr::NonNull,
};

struct AllocatorNode<A> {
    allocator: A,
    next_allocator: AllocatorRef<A>,
}

impl<A: Allocator> AllocatorNode<A> {
    const fn new(allocator: A) -> Self {
        Self {
            allocator,
            next_allocator: AllocatorRef::new(None),
        }
    }

    const fn with_next(allocator: A, next: NonNull<Self>) -> Self {
        Self {
            allocator,
            next_allocator: AllocatorRef::new(Some(next)),
        }
    }
}

type AllocatorRef<A> = Cell<Option<NonNull<AllocatorNode<A>>>>;

pub struct ChainAllocator<A> {
    next_allocator: AllocatorRef<A>,
    _owns: PhantomData<A>,
}

impl<A> Drop for ChainAllocator<A> {
    fn drop(&mut self) {
        while let Some(alloc_node_ptr) = self.next_allocator.get() {
            // SAFETY: alloc_node_ptr was allocated using `Box` and it's never dereferenced again
            let alloc_node = unsafe { Box::from_raw(alloc_node_ptr.as_ptr()) };
            self.next_allocator
                .set(alloc_node.next_allocator.into_inner());
        }
    }
}

unsafe impl<A> Allocator for ChainAllocator<A>
where
    A: Allocator + Default,
{
    #[inline]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        match self.next_allocator.get() {
            None => {
                let allocator = A::default();
                let allocator_node = Box::try_new(AllocatorNode::new(allocator))?;

                self.allocate_and_track_node(allocator_node, layout)
            }
            Some(next_allocator_node_ptr) => {
                // SAFETY: Should be safe because ChainAllocator is not `Sync` and `Send`
                let next_allocator_node = unsafe { next_allocator_node_ptr.as_ref() };

                if let Ok(buf_ptr) = next_allocator_node.allocator.allocate(layout) {
                    Ok(buf_ptr)
                } else {
                    let allocator = A::default();

                    let allocator_node =
                        Box::try_new(AllocatorNode::with_next(allocator, next_allocator_node_ptr))?;

                    self.allocate_and_track_node(allocator_node, layout)
                }
            }
        }
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let (header_layout, buf_offset) =
            Layout::new::<AllocationHeader<A>>().extend(layout).unwrap();

        let header_ptr = ptr.as_ptr().sub(buf_offset).cast();
        let header: AllocationHeader<A> = core::ptr::read(header_ptr);

        header
            .allocator_node
            .as_ref()
            .allocator
            .deallocate(NonNull::new_unchecked(header_ptr.cast()), header_layout);
    }
}

#[repr(transparent)]
struct AllocationHeader<A> {
    allocator_node: NonNull<AllocatorNode<A>>,
}

impl<A: Allocator> ChainAllocator<A> {
    fn allocate_and_track_node(
        &self,
        allocator_node: Box<AllocatorNode<A>>,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    where
        A: Allocator,
    {
        let (header_layout, buf_offset) =
            Layout::new::<AllocationHeader<A>>().extend(layout).unwrap();

        let buf_ptr = allocator_node
            .allocator
            .allocate(header_layout)?
            .cast::<u8>();

        let allocator_node_ptr = NonNull::from(Box::leak(allocator_node));

        // SAFETY: buf_ptr is valid because allocation succeeded
        unsafe {
            core::ptr::write(
                buf_ptr.cast().as_ptr(),
                AllocationHeader::<A> {
                    allocator_node: allocator_node_ptr,
                },
            );
        };

        self.next_allocator.set(Some(allocator_node_ptr));

        Ok({
            // SAFETY: buf_ptr + buf_offset is in bounds and non-null
            let ptr = unsafe { NonNull::new_unchecked(buf_ptr.as_ptr().add(buf_offset)) };

            NonNull::slice_from_raw_parts(ptr, layout.size())
        })
    }
}

impl<A> ChainAllocator<A> {
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        Self {
            next_allocator: AllocatorRef::new(None),
            _owns: PhantomData,
        }
    }
}

#[cfg(test)]
mod test {
    use std::mem::size_of;

    use crate::linear_allocator::LinearAllocator;

    use super::*;

    #[test]
    fn should_create_multiple_allocators() {
        let linear_allocator = ChainAllocator::<LinearAllocator<{ 64 * size_of::<i32>() }>>::new();

        let mut vec1 = Vec::with_capacity_in(32, &linear_allocator);
        let mut vec2 = Vec::with_capacity_in(32, &linear_allocator);

        vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
        vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

        assert_eq!(vec1, &[1, 2, 3, 4, 5]);
        assert_eq!(vec2, &[6, 7, 8, 9, 10]);
    }

    #[test]
    fn should_reuse_block() {
        let linear_allocator =
            ChainAllocator::<LinearAllocator<{ 1024 * size_of::<i32>() }>>::new();
        let vec1: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);

        drop(vec1);

        let vec2: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);
        drop(vec2);
    }
}
