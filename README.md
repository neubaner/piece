# Piece
[![Crates.io](https://img.shields.io/crates/v/piece)](https://crates.io/crates/piece)
[![Documentation](https://docs.rs/piece/badge.svg)](https://docs.rs/piece)

Piece is a collection of composable allocators for rust. 

## Allocators
Currently this crate contains two allocators, `piece::LinearAllocator` and `piece::ChainAllocator`.

### Linear allocator
`piece::LinearAllocator` is an allocator that keeps a fixed-sized buffer internally
and use it to make allocations. Once the buffer is full, all next allocations fails.

This allocator is useful when you want a "scratch space" for multiple tiny allocations
that share the same lifetime.

Usage:
```rust
#![cfg_attr(not(feature = "stable"), feature(allocator_api))]
#[cfg(feature = "vec")]
{
    use core::mem::size_of;

    use piece::vec::Vec;
    use piece::LinearAllocator;

    let linear_allocator = LinearAllocator::with_capacity(64 * size_of::<i32>());

    let mut vec1 = Vec::with_capacity_in(32, &linear_allocator);
    let mut vec2 = Vec::with_capacity_in(32, &linear_allocator);

    vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
    vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

    assert_eq!(vec1, &[1, 2, 3, 4, 5]);
    assert_eq!(vec2, &[6, 7, 8, 9, 10]);
}
```

### Chain allocator
A `piece::ChainAllocator` create a new allocator of type `A` when the existing allocators of this

It can be useful when used with a `piece::LinearAllocator` for example. When
all of its memory is used, the `ChainAllocator` will create a new one. This is useful when
you want to use fixed-sized allocators but you're worried that your program will run out of
memory.

Usage:
```rust
#![cfg_attr(not(feature = "stable"), feature(allocator_api))]
#[cfg(feature="vec")]
{
    use core::mem::size_of;

    use piece::vec::Vec;
    use piece::LinearAllocator;
    use piece::ChainAllocator;

    // Make room for the allocator pointer
    let chain_allocator = ChainAllocator::new(|| {
        LinearAllocator::with_capacity(32 * size_of::<i32>() + size_of::<*const ()>())
    });

    // Create two vectors that fills the whole `LinearAllocator` so
    // each `Vec` creates a new allocator
    let mut vec1 = Vec::with_capacity_in(32, &chain_allocator);
    let mut vec2 = Vec::with_capacity_in(32, &chain_allocator);

    vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
    vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

    assert_eq!(vec1, &[1, 2, 3, 4, 5]);
    assert_eq!(vec2, &[6, 7, 8, 9, 10]);

    assert_eq!(2, chain_allocator.allocator_count());
}
```
## Nightly channel
You should enable the Rust `feature_api` on nightly builds adding `#![feature(allocator_api)]` to the root of your crate.

## Stable channel
To use this library on stable channels, you should enable the feature `stable`. It will enable `piece` to use [`allocator_api2`](https://crates.io/crates/allocator-api2),
that contains a mirror of the unstable nightly `Allocator` trait. You should be able to use any collections that are generic over `allocator_api2::Allocator`.
