# Piece

Piece is a collection of composable allocators for rust. 

## Allocators
Currently this crate contains two allocators, `piece::LinearAllocator` and `piece::ChainAllocator`.

### Linear allocator
`piece::LinearAllocator` is an allocator that keeps a fixed-sized buffer internally
and use it to make allocations. Once the buffer is full, all next allocations fails.

This allocator is useful when you want a "scratch space" for multiple tiny allocations
that share the same lifetime.


### Chain allocator
A `piece::ChainAllocator<A>` create a new allocator of type `A` when the existing allocators of this

It can be useful when used with a `piece::LinearAllocator` for example. When
all of its memory is used, the `ChainAllocator` will create a new one. This is useful when
you want to use fixed-sized allocators but you're worried that your program will run out of
memory.

