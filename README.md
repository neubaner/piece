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
#![feature(allocator_api)]

use core::{alloc::Allocator, mem::size_of};
use std::vec::Vec;

use piece::LinearAllocator;

let linear_allocator = LinearAllocator::with_capacity(64 * size_of::<i32>());

let mut vec1 = Vec::with_capacity_in(32, linear_allocator.by_ref());
let mut vec2 = Vec::with_capacity_in(32, linear_allocator.by_ref());

vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

assert_eq!(vec1, &[1, 2, 3, 4, 5]);
assert_eq!(vec2, &[6, 7, 8, 9, 10]);
```

### Chain allocator
A `piece::ChainAllocator` create a new allocator of type `A` when the existing allocators of this

It can be useful when used with a `piece::LinearAllocator` for example. When
all of its memory is used, the `ChainAllocator` will create a new one. This is useful when
you want to use fixed-sized allocators but you're worried that your program will run out of
memory.

Usage:
```rust
#![feature(allocator_api)]

use core::{alloc::Allocator, mem::size_of};
use std::vec::Vec;

use piece::LinearAllocator;
use piece::ChainAllocator;

// Make room for the allocator pointer
let chain_allocator = ChainAllocator::new(|| {
    LinearAllocator::with_capacity(32 * size_of::<i32>() + size_of::<*const ()>())
});

// Create two vectors that fills the whole `LinearAllocator` so
// each `Vec` creates a new allocator
let mut vec1 = Vec::with_capacity_in(32, chain_allocator.by_ref());
let mut vec2 = Vec::with_capacity_in(32, chain_allocator.by_ref());

vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

assert_eq!(vec1, &[1, 2, 3, 4, 5]);
assert_eq!(vec2, &[6, 7, 8, 9, 10]);

assert_eq!(2, chain_allocator.allocator_count());
```
