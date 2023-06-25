#![feature(allocator_api)]
#![warn(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::std_instead_of_core
)]
//! # About
//! A collection of composable allocators.

mod chain_allocator;
mod linear_allocator;

pub use chain_allocator::ChainAllocator;
pub use linear_allocator::LinearAllocator;
