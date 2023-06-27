#![no_std]
#![cfg_attr(not(feature = "stable"), feature(allocator_api))]
#![warn(clippy::all, clippy::std_instead_of_core, clippy::cargo)]
#![doc = include_str!("../README.md")]

extern crate alloc as alloc_crate;

#[cfg(feature = "boxed")]
pub mod boxed;

#[cfg(feature = "vec")]
pub mod vec;

mod alloc;
mod chain_allocator;
mod linear_allocator;

pub use chain_allocator::ChainAllocator;
pub use linear_allocator::LinearAllocator;
