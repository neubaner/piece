#![feature(allocator_api)]
#![warn(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::std_instead_of_core
)]

pub mod chain_allocator;
pub mod linear_allocator;
