#![cfg_attr(not(feature = "stable"), feature(allocator_api))]
#![cfg(feature = "vec")]

use core::mem::size_of;
use piece::LinearAllocator;

#[test]
fn should_keep_allocation_for_the_lifetime() {
    use piece::vec::Vec;

    let linear_allocator = LinearAllocator::with_capacity(1024 * size_of::<i32>());

    let mut vec1 = Vec::with_capacity_in(32, &linear_allocator);
    let mut vec2 = Vec::with_capacity_in(32, &linear_allocator);
    let mut zero_sized_vec = Vec::new_in(&linear_allocator);

    vec1.extend_from_slice(&[1, 2, 3, 4, 5]);
    vec2.extend_from_slice(&[6, 7, 8, 9, 10]);

    zero_sized_vec.push(());
    zero_sized_vec.push(());
    zero_sized_vec.push(());

    assert_eq!(linear_allocator.allocated_bytes(), 64 * size_of::<i32>());
    assert_eq!(vec1, &[1, 2, 3, 4, 5]);
    assert_eq!(vec2, &[6, 7, 8, 9, 10]);
    assert_eq!(zero_sized_vec.len(), 3);
}

#[test]
fn should_reuse_block() {
    use piece::vec::Vec;

    let linear_allocator = LinearAllocator::with_capacity(1024 * size_of::<i32>());
    let vec1: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);

    drop(vec1);

    let vec2: Vec<i32, _> = Vec::with_capacity_in(512, &linear_allocator);
    drop(vec2);

    assert_eq!(linear_allocator.allocated_bytes(), 1024 * size_of::<i32>());
}

#[test]
fn linear_allocator_should_work_on_a_multithread_environment() {
    use piece::vec::Vec;

    let linear_allocator = LinearAllocator::with_capacity(1024 * 1024 * 1024);

    std::thread::scope(|s| {
        let linear_allocator = &linear_allocator;
        for i in 1..10000 {
            s.spawn(move || {
                let mut vec: Vec<i32, _> = Vec::with_capacity_in(1024, linear_allocator);
                let slice: Vec<i32> = (i..i + 1024).collect();
                vec.extend(slice.iter());

                assert_eq!(vec, slice);
            });
        }
    })
}
