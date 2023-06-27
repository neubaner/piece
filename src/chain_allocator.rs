use crate::alloc::{AllocError, Allocator};

#[cfg(not(feature = "boxed"))]
use alloc_crate::boxed::Box;

#[cfg(feature = "boxed")]
use crate::boxed::Box;

use core::{alloc::Layout, cell::Cell, marker::PhantomData, ptr::NonNull};

struct AllocatorNode<A> {
    allocator: A,
    next_allocator: AllocatorRef<A>,
    _owns: PhantomData<AllocatorNode<A>>,
}

impl<A: Allocator> AllocatorNode<A> {
    fn new(allocator: A) -> Self {
        Self {
            allocator,
            next_allocator: AllocatorRef::new(None),
            _owns: PhantomData,
        }
    }

    fn with_next(allocator: A, next: NonNull<Self>) -> Self {
        Self {
            allocator,
            next_allocator: AllocatorRef::new(Some(next)),
            _owns: PhantomData,
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

    unsafe fn grow_and_track(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let (old_layout_with_footer, _) = old_layout
            .extend(Layout::new::<AllocationFooter<A>>())
            .unwrap();

        let (new_layout_with_footer, footer_offset) = new_layout
            .extend(Layout::new::<AllocationFooter<A>>())
            .unwrap();

        let buf_ptr = unsafe {
            self.allocator
                .grow(ptr, old_layout_with_footer, new_layout_with_footer)
        }?
        .cast::<u8>();

        // SAFETY: buf_ptr is valid because allocation succeeded
        unsafe {
            core::ptr::write(
                buf_ptr.as_ptr().add(footer_offset).cast(),
                AllocationFooter::<A> {
                    allocator_node: NonNull::from(self),
                },
            );
        };

        Ok(NonNull::slice_from_raw_parts(buf_ptr, new_layout.size()))
    }

    unsafe fn grow_zeroed_and_track(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let (old_layout_with_footer, old_footer_offset) = old_layout
            .extend(Layout::new::<AllocationFooter<A>>())
            .unwrap();

        let (new_layout_with_footer, new_footer_offset) = new_layout
            .extend(Layout::new::<AllocationFooter<A>>())
            .unwrap();

        let buf_ptr = unsafe {
            self.allocator
                .grow_zeroed(ptr, old_layout_with_footer, new_layout_with_footer)
        }?
        .cast::<u8>();

        // Zero the previous pointer location
        // SAFETY: buffer returned should be bigger than the previous one.
        unsafe {
            core::ptr::write_bytes(
                buf_ptr.as_ptr().add(old_footer_offset),
                0,
                core::mem::size_of::<AllocationFooter<A>>(),
            );
        };

        // SAFETY: buf_ptr is valid because allocation succeeded
        unsafe {
            core::ptr::write(
                buf_ptr.as_ptr().add(new_footer_offset).cast(),
                AllocationFooter::<A> {
                    allocator_node: NonNull::from(self),
                },
            );
        };

        Ok(NonNull::slice_from_raw_parts(buf_ptr, new_layout.size()))
    }

    unsafe fn shrink_and_track(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        let (old_layout_with_footer, _) = old_layout
            .extend(Layout::new::<AllocationFooter<A>>())
            .unwrap();

        let (new_layout_with_footer, footer_offset) = new_layout
            .extend(Layout::new::<AllocationFooter<A>>())
            .unwrap();

        let buf_ptr = unsafe {
            self.allocator
                .shrink(ptr, old_layout_with_footer, new_layout_with_footer)
        }?
        .cast::<u8>();

        // SAFETY: buf_ptr is valid because allocation succeeded
        unsafe {
            core::ptr::write(
                buf_ptr.as_ptr().add(footer_offset).cast(),
                AllocationFooter::<A> {
                    allocator_node: NonNull::from(self),
                },
            );
        };

        Ok(NonNull::slice_from_raw_parts(buf_ptr, new_layout.size()))
    }

    // SAFETY: layout and ptr have been used before to make an allocation
    unsafe fn ref_from_allocation<'a>(layout: Layout, ptr: NonNull<u8>) -> (Layout, &'a Self) {
        let (layout_with_footer, footer_offset) = layout.extend(Layout::new::<Self>()).unwrap();

        let footer_ptr: *mut AllocationFooter<A> = ptr.as_ptr().add(footer_offset).cast();

        let allocator_node = NonNull::new_unchecked(footer_ptr)
            .as_ref()
            .allocator_node
            .as_ref();

        (layout_with_footer, allocator_node)
    }
}

type AllocatorRef<A> = Cell<Option<NonNull<AllocatorNode<A>>>>;

/// A [`ChainAllocator<A>`] create a new allocator of type `A` when the existing allocators of this
/// type are exausted.
///
/// It can be useful when used with a [`LinearAllocator`] for example. When
/// all of its memory is used, the [`ChainAllocator`] will create a new one. This is useful when
/// you want to use fixed-sized allocators but you're worried that your program will run out of
/// memory.
///
/// There's some overhead when using the [`ChainAllocator`]. Currently, every allocation has an
/// extra pointer that refers to the allocator, to make deallocation possible. Also the allocators
/// themselves are allocated using the [`Box`].
///
/// # Usage:
/// ```
/// #![cfg_attr(not(feature = "stable"), feature(allocator_api))]
/// #[cfg(feature="vec")]
/// {
///     use core::mem::size_of;
///
///     use piece::vec::Vec;
///     use piece::LinearAllocator;
///     use piece::ChainAllocator;
///
///     // Make room for the allocator pointer
///     let chain_allocator = ChainAllocator::new(|| {
///         LinearAllocator::with_capacity(32 * size_of::<i32>() + size_of::<*const ()>())
///     });
///
///     // Create two vectors that fills the whole `LinearAllocator` so
///     // each `Vec` creates a new allocator
///     let mut vec1 = Vec::with_capacity_in(32, &chain_allocator);
///     let mut vec2 = Vec::with_capacity_in(32, &chain_allocator);
///
///     vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
///     vec2.extend_from_slice(&[6, 7, 8, 9, 10]);
///
///     assert_eq!(vec1, &[1, 2, 3, 4, 5]);
///     assert_eq!(vec2, &[6, 7, 8, 9, 10]);
///
///     assert_eq!(2, chain_allocator.allocator_count());
/// }
/// ```
///
/// [`LinearAllocator`]: crate::LinearAllocator
pub struct ChainAllocator<A, F> {
    next_allocator: AllocatorRef<A>,
    _owns: PhantomData<AllocatorNode<A>>,
    allocator_factory: F,
}

// SAFETY: It's safe to send them across threads because there's no way to get a references to
// allocation nodes, so no alias happens
unsafe impl<A: Send, F> Send for ChainAllocator<A, F> {}

impl<A, F> Drop for ChainAllocator<A, F> {
    fn drop(&mut self) {
        while let Some(alloc_node_ptr) = self.next_allocator.get() {
            // SAFETY: alloc_node_ptr was allocated using `Box` and it's never dereferenced again
            let alloc_node = unsafe { Box::from_raw(alloc_node_ptr.as_ptr()) };
            self.next_allocator.set(alloc_node.next_allocator.get());
        }
    }
}

unsafe impl<A, F> Allocator for ChainAllocator<A, F>
where
    A: Allocator,
    F: Fn() -> A,
{
    #[inline]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        // No need to track zero size allocators(like Global), they are already free to create and
        // all instances should be the same
        if core::mem::size_of::<A>() == 0 {
            let zero_sized_allocator = (self.allocator_factory)();
            return zero_sized_allocator.allocate(layout);
        }

        match self.next_allocator.get() {
            Some(next_allocator_node_ptr) => {
                // SAFETY: Should be safe because ChainAllocator is not `Sync` and `Send`
                let next_allocator_node = unsafe { next_allocator_node_ptr.as_ref() };

                match next_allocator_node.allocate_and_track(layout) {
                    Ok(buf_ptr) => Ok(buf_ptr),
                    Err(_) => {
                        let allocator = (self.allocator_factory)();
                        let allocator_node =
                            AllocatorNode::with_next(allocator, next_allocator_node_ptr);

                        self.allocate_and_track_node(allocator_node, layout)
                    }
                }
            }
            None => {
                let allocator = (self.allocator_factory)();
                let allocator_node = AllocatorNode::new(allocator);

                self.allocate_and_track_node(allocator_node, layout)
            }
        }
    }

    #[inline]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        // No need to track zero size allocators(like Global), they are already free to create and
        // all instances should be the same

        if core::mem::size_of::<A>() == 0 {
            let zero_sized_allocator = (self.allocator_factory)();
            return zero_sized_allocator.deallocate(ptr, layout);
        }

        let (layout_with_footer, allocator_node) =
            AllocatorNode::<A>::ref_from_allocation(layout, ptr);

        allocator_node.allocator.deallocate(ptr, layout_with_footer);
    }

    unsafe fn grow(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() >= old_layout.size(),
            "`new_layout.size()` must be greater than or equal to `old_layout.size()`"
        );

        if core::mem::size_of::<A>() == 0 {
            let zero_sized_allocator = (self.allocator_factory)();
            return zero_sized_allocator.grow(ptr, old_layout, new_layout);
        }

        let (_, allocator_node) = AllocatorNode::<A>::ref_from_allocation(old_layout, ptr);

        if let Ok(ptr) = allocator_node.grow_and_track(ptr, old_layout, new_layout) {
            return Ok(ptr);
        }

        let new_ptr = self.allocate(new_layout)?;

        // SAFETY: because `new_layout.size()` must be greater than or equal to
        // `old_layout.size()`, both the old and new memory allocation are valid for reads and
        // writes for `old_layout.size()` bytes. Also, because the old allocation wasn't yet
        // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
        // safe. The safety contract for `dealloc` must be upheld by the caller.
        unsafe {
            core::ptr::copy_nonoverlapping(
                ptr.as_ptr(),
                new_ptr.cast().as_ptr(),
                old_layout.size(),
            );
            self.deallocate(ptr, old_layout);
        }

        Ok(new_ptr)
    }

    unsafe fn grow_zeroed(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() >= old_layout.size(),
            "`new_layout.size()` must be greater than or equal to `old_layout.size()`"
        );

        if core::mem::size_of::<A>() == 0 {
            let zero_sized_allocator = (self.allocator_factory)();
            return zero_sized_allocator.grow_zeroed(ptr, old_layout, new_layout);
        }

        let (_, allocator_node) = AllocatorNode::<A>::ref_from_allocation(old_layout, ptr);

        if let Ok(ptr) = allocator_node.grow_zeroed_and_track(ptr, old_layout, new_layout) {
            return Ok(ptr);
        }

        let new_ptr = self.allocate_zeroed(new_layout)?;

        // SAFETY: because `new_layout.size()` must be greater than or equal to
        // `old_layout.size()`, both the old and new memory allocation are valid for reads and
        // writes for `old_layout.size()` bytes. Also, because the old allocation wasn't yet
        // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
        // safe. The safety contract for `dealloc` must be upheld by the caller.
        unsafe {
            core::ptr::copy_nonoverlapping(
                ptr.as_ptr(),
                new_ptr.cast().as_ptr(),
                old_layout.size(),
            );
            self.deallocate(ptr, old_layout);
        }

        Ok(new_ptr)
    }

    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        debug_assert!(
            new_layout.size() <= old_layout.size(),
            "`new_layout.size()` must be smaller than or equal to `old_layout.size()`"
        );

        if core::mem::size_of::<A>() == 0 {
            let zero_sized_allocator = (self.allocator_factory)();
            return zero_sized_allocator.grow_zeroed(ptr, old_layout, new_layout);
        }

        let (_, allocator_node) = AllocatorNode::<A>::ref_from_allocation(old_layout, ptr);

        if let Ok(ptr) = allocator_node.shrink_and_track(ptr, old_layout, new_layout) {
            return Ok(ptr);
        }

        let new_ptr = self.allocate(new_layout)?;

        // SAFETY: because `new_layout.size()` must be lower than or equal to
        // `old_layout.size()`, both the old and new memory allocation are valid for reads and
        // writes for `new_layout.size()` bytes. Also, because the old allocation wasn't yet
        // deallocated, it cannot overlap `new_ptr`. Thus, the call to `copy_nonoverlapping` is
        // safe. The safety contract for `dealloc` must be upheld by the caller.
        unsafe {
            core::ptr::copy_nonoverlapping(
                ptr.as_ptr(),
                new_ptr.cast().as_ptr(),
                new_layout.size(),
            );
            self.deallocate(ptr, old_layout);
        }

        Ok(new_ptr)
    }
}

#[repr(transparent)]
struct AllocationFooter<A> {
    allocator_node: NonNull<AllocatorNode<A>>,
}

impl<A: Allocator, F> ChainAllocator<A, F> {
    fn allocate_and_track_node(
        &self,
        allocator_node: AllocatorNode<A>,
        layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError>
    where
        A: Allocator,
    {
        #[cfg(feature = "boxed")]
        let allocator_node = Box::try_new(allocator_node)?;

        #[cfg(not(feature = "boxed"))]
        let allocator_node = Box::new(allocator_node);

        let allocation = allocator_node.allocate_and_track(layout)?;

        // SAFETY: pointers from `Box` are always valid
        self.next_allocator.set(Some(unsafe {
            NonNull::new_unchecked(Box::into_raw(allocator_node))
        }));

        Ok(allocation)
    }
}

impl<A, F> ChainAllocator<A, F>
where
    F: Fn() -> A,
{
    /// Creates a empty [`ChainAllocator<A>`]. `allocator_factory` should create a fresh allocator.
    #[inline]
    #[must_use]
    pub const fn new(allocator_factory: F) -> Self {
        Self {
            next_allocator: AllocatorRef::new(None),
            allocator_factory,
            _owns: PhantomData,
        }
    }

    /// Returns the number of allocators created by this [`ChainAllocator<A>`].
    pub fn allocator_count(&self) -> usize {
        let mut next_allocator = self.next_allocator.get();

        let mut count = 0;
        while let Some(alloc_node_ptr) = next_allocator {
            // SAFETY: it's not possible to get a reference to an allocation node outside the
            // crate
            next_allocator = unsafe { alloc_node_ptr.as_ref() }.next_allocator.get();
            count += 1;
        }
        count
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::linear_allocator::LinearAllocator;
    use core::mem::size_of;

    #[test]
    fn should_alloc_zeroed() {
        let chain_allocator =
            ChainAllocator::new(|| LinearAllocator::with_capacity(32 + size_of::<*const ()>()));

        let layout = Layout::array::<u8>(32).unwrap();
        let allocation = chain_allocator.allocate_zeroed(layout).unwrap();

        let slice = unsafe { allocation.as_ref() };
        assert_eq!(slice.len(), 32);
        assert_eq!(slice, [0; 32]);
        assert_eq!(chain_allocator.allocator_count(), 1);

        unsafe { chain_allocator.deallocate(allocation.cast(), layout) };
    }

    #[test]
    fn should_grow_allocation() {
        let chain_allocator =
            ChainAllocator::new(|| LinearAllocator::with_capacity(128 + size_of::<*const ()>()));

        let old_layout = Layout::array::<u8>(32).unwrap();
        let old_allocation = chain_allocator.allocate(old_layout).unwrap();

        let new_layout = Layout::array::<u8>(64).unwrap();

        let new_allocation = unsafe {
            chain_allocator
                .grow(old_allocation.cast(), old_layout, new_layout)
                .unwrap()
        };

        let slice = unsafe { new_allocation.as_ref() };
        assert_eq!(slice.len(), 64);

        unsafe { chain_allocator.deallocate(new_allocation.cast(), new_layout) };
    }

    #[test]
    fn should_grow_zeroed_allocation() {
        let chain_allocator =
            ChainAllocator::new(|| LinearAllocator::with_capacity(128 + size_of::<*const ()>()));

        let old_layout = Layout::array::<u8>(32).unwrap();
        let mut old_allocation = chain_allocator.allocate(old_layout).unwrap();

        {
            let slice = unsafe { old_allocation.as_mut() };
            slice.fill(1);
            assert_eq!(slice, [1; 32]);
        }

        let new_layout = Layout::array::<u8>(64).unwrap();
        let new_allocation = unsafe {
            chain_allocator
                .grow_zeroed(old_allocation.cast(), old_layout, new_layout)
                .unwrap()
        };

        let slice = unsafe { new_allocation.as_ref() };

        assert_eq!(slice.len(), 64);
        assert_eq!(slice[..32], [1; 32]);
        assert_eq!(slice[32..], [0; 32]);

        unsafe { chain_allocator.deallocate(new_allocation.cast(), new_layout) };
    }

    #[test]
    fn should_shrink_allocation() {
        let chain_allocator =
            ChainAllocator::new(|| LinearAllocator::with_capacity(128 + size_of::<*const ()>()));

        let old_layout = Layout::array::<u8>(64).unwrap();
        let mut old_allocation = chain_allocator.allocate(old_layout).unwrap();

        {
            let slice = unsafe { old_allocation.as_mut() };
            slice.fill(1);
            assert_eq!(slice, [1; 64]);
        }

        let new_layout = Layout::array::<u8>(32).unwrap();
        let new_allocation = unsafe {
            chain_allocator
                .shrink(old_allocation.cast(), old_layout, new_layout)
                .unwrap()
        };

        let slice = unsafe { new_allocation.as_ref() };

        assert_eq!(slice.len(), 32);
        assert_eq!(slice, [1; 32]);

        unsafe { chain_allocator.deallocate(new_allocation.cast(), new_layout) };
    }
}
