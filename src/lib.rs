#![feature(allocator_api)]

mod linear_allocator;

use std::{
    alloc::{AllocError, Allocator, Layout},
    cell::Cell,
    marker::PhantomData,
    ptr::NonNull,
};

struct AllocatorNode<A> {
    allocator: A,
    allocations: Vec<NonNull<u8>>,
    next_allocator: AllocatorRef<A>,
}

impl<A: Allocator> AllocatorNode<A> {
    fn new(allocator: A) -> Self {
        Self {
            allocator,
            allocations: Vec::new(),
            next_allocator: AllocatorRef::new(None),
        }
    }

    fn with_next(allocator: A, next: NonNull<AllocatorNode<A>>) -> Self {
        Self {
            allocator,
            allocations: Vec::new(),
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
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        match self.next_allocator.get() {
            None => {
                let allocator = A::default();
                let allocator_node = Box::try_new(AllocatorNode::new(allocator))?;

                self.allocate_and_track_node(allocator_node, layout)
            }
            Some(mut next_allocator_node_ptr) => {
                let next_allocator_node = unsafe { next_allocator_node_ptr.as_mut() };
                match next_allocator_node.allocator.allocate(layout) {
                    Ok(buf_ptr) => Ok(buf_ptr),
                    Err(_) => {
                        let allocator = A::default();

                        let allocator_node = Box::try_new(AllocatorNode::with_next(
                            allocator,
                            next_allocator_node_ptr,
                        ))?;

                        self.allocate_and_track_node(allocator_node, layout)
                    }
                }
            }
        }
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let mut next_allocator = self.next_allocator.get();

        while let Some(mut alloc_node_ptr) = next_allocator {
            // SAFETY: guaranteed to not have an alias in single thread
            let alloc_node = unsafe { alloc_node_ptr.as_mut() };

            if alloc_node.allocations.contains(&ptr) {
                alloc_node.allocator.deallocate(ptr, layout);
                break;
            }

            next_allocator = alloc_node.next_allocator.get();
        }
    }
}

impl<A> ChainAllocator<A> {
    #[inline]
    pub const fn new() -> Self {
        Self {
            next_allocator: AllocatorRef::new(None),
            _owns: PhantomData,
        }
    }
}

impl<A: Allocator> ChainAllocator<A> {
    fn allocate_and_track_node(
        &self,
        mut allocator_node: Box<AllocatorNode<A>>,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    where
        A: Allocator,
    {
        let buf_ptr = allocator_node.allocator.allocate(layout)?;

        {
            // SAFETY:
            let ptr = unsafe { buf_ptr.as_ref() }.as_ptr().cast_mut();
            allocator_node
                .allocations
                .push(unsafe { NonNull::new_unchecked(ptr) });
        }

        let allocator_node_ptr = Box::into_raw(allocator_node);
        // SAFETY: `Box::into_raw` always returns non-null pointer
        self.next_allocator
            .set(Some(unsafe { NonNull::new_unchecked(allocator_node_ptr) }));

        Ok(buf_ptr)
    }
}

#[cfg(test)]
mod test {
    use std::mem::size_of;

    use crate::linear_allocator::LinearAllocator;

    use super::*;

    #[test]
    fn should_create_multiple_allocators() {
        let linear_allocator = ChainAllocator::<LinearAllocator<{ 32 * size_of::<i32>() }>>::new();

        let mut vec1 = Vec::with_capacity_in(32, &linear_allocator);
        let mut vec2 = Vec::with_capacity_in(32, &linear_allocator);

        vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
        vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

        assert_eq!(vec1, &[1, 2, 3, 4, 5]);
        assert_eq!(vec2, &[6, 7, 8, 9, 10]);
    }

    #[test]
    fn should_reuse_block() {
        let linear_allocator = ChainAllocator::<LinearAllocator<{ 512 * size_of::<i32>() }>>::new();
        let vec1: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);

        drop(vec1);

        let vec2: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);
        drop(vec2);
    }
}
