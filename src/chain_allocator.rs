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

    fn allocate_and_track(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let (layout_with_footer, footer_offset) =
            layout.extend(Layout::new::<AllocationFooter<A>>()).unwrap();

        let buf_ptr = self.allocator.allocate(layout_with_footer)?.cast::<u8>();

        // SAFETY: buf_ptr is valid because allocation succeeded
        unsafe {
            core::ptr::write(
                buf_ptr.as_ptr().add(footer_offset).cast(),
                AllocationFooter::<A> {
                    allocator_node: NonNull::from(self),
                },
            );
        };

        Ok(NonNull::slice_from_raw_parts(buf_ptr, layout.size()))
    }
}

type AllocatorRef<A> = Cell<Option<NonNull<AllocatorNode<A>>>>;

pub struct ChainAllocator<A> {
    next_allocator: AllocatorRef<A>,
    _owns: PhantomData<A>,
}

// SAFETY: It's safe to send them across threads because there's no way to get a references to
// allocation nodes, so no alias happens
unsafe impl<A: Send> Send for ChainAllocator<A> {}

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
                let allocator_node = AllocatorNode::new(allocator);

                self.allocate_and_track_node(allocator_node, layout)
            }
            Some(next_allocator_node_ptr) => {
                // SAFETY: Should be safe because ChainAllocator is not `Sync` and `Send`
                let next_allocator_node = unsafe { next_allocator_node_ptr.as_ref() };

                if let Ok(buf_ptr) = next_allocator_node.allocate_and_track(layout) {
                    Ok(buf_ptr)
                } else {
                    let allocator = A::default();

                    let allocator_node =
                        AllocatorNode::with_next(allocator, next_allocator_node_ptr);

                    self.allocate_and_track_node(allocator_node, layout)
                }
            }
        }
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        let (layout_with_footer, footer_offset) =
            layout.extend(Layout::new::<AllocationFooter<A>>()).unwrap();

        let footer_ptr = ptr.as_ptr().sub(footer_offset).cast();
        let footer: AllocationFooter<A> = core::ptr::read(footer_ptr);

        footer
            .allocator_node
            .as_ref()
            .allocator
            .deallocate(ptr, layout_with_footer);
    }
}

#[repr(transparent)]
struct AllocationFooter<A> {
    allocator_node: NonNull<AllocatorNode<A>>,
}

impl<A: Allocator> ChainAllocator<A> {
    fn allocate_and_track_node(
        &self,
        allocator_node: AllocatorNode<A>,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    where
        A: Allocator,
    {
        let allocation = allocator_node.allocate_and_track(layout)?;
        let allocator_node_ptr = NonNull::from(Box::leak(Box::try_new(allocator_node)?));

        self.next_allocator.set(Some(allocator_node_ptr));

        Ok(allocation)
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

    pub fn allocators_count(&self) -> usize {
        let mut next_allocator = self.next_allocator.get();

        let mut count = 0;
        while let Some(alloc_node_ptr) = next_allocator {
            // SAFETY: it's not possible to get a reference of an allocation node outside the
            // crate
            next_allocator = unsafe { alloc_node_ptr.as_ref() }.next_allocator.get();
            count += 1;
        }
        count
    }
}

#[cfg(test)]
mod test {
    use std::mem::size_of;

    use crate::linear_allocator::LinearAllocator;

    use super::*;

    #[test]
    fn should_create_a_new_allocator_when_needed() {
        // NOTE(gneubaner): each allocation has a pointer to the allocator used
        let chain_allocator = ChainAllocator::<
            LinearAllocator<{ 32 * size_of::<i32>() + size_of::<*const ()>() }>,
        >::new();

        let mut vec1 = Vec::with_capacity_in(32, &chain_allocator);
        let mut vec2 = Vec::with_capacity_in(32, &chain_allocator);

        vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
        vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

        assert_eq!(vec1, &[1, 2, 3, 4, 5]);
        assert_eq!(vec2, &[6, 7, 8, 9, 10]);
        assert_eq!(2, chain_allocator.allocators_count());
    }

    #[test]
    fn should_reuse_the_same_allocator() {
        // NOTE(gneubaner): each allocation has a pointer to the allocator used
        let chain_allocator = ChainAllocator::<
            LinearAllocator<{ 1024 * size_of::<i32>() + size_of::<*const ()>() }>,
        >::new();

        let mut vec1 = Vec::with_capacity_in(32, &chain_allocator);
        let mut vec2 = Vec::with_capacity_in(32, &chain_allocator);

        vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
        vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

        assert_eq!(vec1, &[1, 2, 3, 4, 5]);
        assert_eq!(vec2, &[6, 7, 8, 9, 10]);
        assert_eq!(1, chain_allocator.allocators_count());
    }

    #[test]
    fn should_be_safe_to_send_across_threads() {
        // NOTE(gneubaner): each allocation has a pointer to the allocator used
        let chain_allocator = ChainAllocator::<
            LinearAllocator<{ 32 * size_of::<i32>() + size_of::<*const ()>() }>,
        >::new();

        let mut vec1 = Vec::with_capacity_in(32, &chain_allocator);
        vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
        assert_eq!(vec1, &[1, 2, 3, 4, 5]);
        drop(vec1);

        let handle = std::thread::spawn(move || {
            let mut vec2 = Vec::with_capacity_in(32, &chain_allocator);
            vec2.extend_from_slice(&[6, 7, 8, 9, 10]);
            assert_eq!(vec2, &[6, 7, 8, 9, 10]);
        });

        let _ = handle.join();
    }
}
