#[cfg(feature = "allocator-api2")]
pub use allocator_api2::boxed::*;

#[cfg(not(feature = "allocator-api2"))]
pub use alloc_crate::boxed::*;
