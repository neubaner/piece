#![feature(allocator_api)]
#![warn(clippy::all, clippy::std_instead_of_core, clippy::cargo)]
#![cfg_attr(not(test), no_std)]
//! # About
//! A collection of composable allocators.

extern crate alloc;

mod chain_allocator;
mod linear_allocator;

pub use chain_allocator::ChainAllocator;
pub use linear_allocator::LinearAllocator;
