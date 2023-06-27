#[cfg(feature = "allocator-api2")]
pub use allocator_api2::vec::*;

#[cfg(not(feature = "allocator-api2"))]
pub use alloc_crate::vec::*;
