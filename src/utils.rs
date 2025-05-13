//! Utility functions used throughout the library.
//!
//! File: rusty-code/src/utils.rs

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

/// Compute a hash value for any hashable type.
///
/// # Examples
///
/// ```
/// use rusty_code::utils::compute_hash;
///
/// let hash = compute_hash(&"test_string");
/// ```
pub fn compute_hash<T: Hash>(t: &T) -> u64 {
    let mut s = DefaultHasher::new();
    t.hash(&mut s);
    s.finish()
}

/// Check if a number is a power of two.
///
/// # Examples
///
/// ```
/// use rusty_code::utils::is_power_of_two;
///
/// assert!(is_power_of_two(16));
/// assert!(!is_power_of_two(15));
/// ```
pub fn is_power_of_two(n: usize) -> bool {
    n != 0 && (n & (n - 1)) == 0
}

/// Calculates the next power of two greater than or equal to `n`
///
/// # Examples
///
/// ```
/// use rusty_code::utils::next_power_of_two;
///
/// assert_eq!(next_power_of_two(13), 16);
/// ```
pub fn next_power_of_two(n: usize) -> usize {
    if n == 0 {
        return 1;
    }
    if is_power_of_two(n) {
        return n;
    }

    // TODO: Implement next power of two calculation
    1 << (std::mem::size_of::<usize>() * 8 - (n - 1).leading_zeros() as usize)
}

// TODO: Add more utility functions as needed
