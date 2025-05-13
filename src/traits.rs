//! Core traits defining behavior for data structures.
//!
//! File: rusty-code/src/traits.rs

use crate::errors::Result;
use std::fmt::Debug;
use std::hash::Hash;

/// The main trait that all data structures must implement.
pub trait DataStructure {
    /// Returns the name of the data structure.
    fn name(&self) -> &str;

    /// Returns the current size (number of elements) in the structure.
    fn size(&self) -> usize;

    /// Returns true if the structure is empty.
    fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Clears all elements from the structure.
    fn clear(&mut self);
}

/// A trait for data structures that support key-value operations.
pub trait KeyValueStore<K, V>: DataStructure
where
    K: Eq + Hash + Clone + Debug,
    V: Clone + Debug,
{
    /// Insert a key-value pair into the structure.
    fn insert(&mut self, key: K, value: V) -> Result<Option<V>>;

    /// Remove a key-value pair from the structure.
    fn remove(&mut self, key: &K) -> Result<Option<V>>;

    /// Get a value associated with a key.
    fn get(&self, key: &K) -> Result<Option<&V>>;

    /// Check if the structure contains a key.
    fn contains_key(&self, key: &K) -> bool;
}

/// A trait for data structures that support collection operations.
pub trait Collection<T>: DataStructure
where
    T: Clone + Debug,
{
    /// Add an element to the collection.
    fn add(&mut self, item: T) -> Result<()>;

    /// Remove an element from the collection.
    fn remove(&mut self, item: &T) -> Result<Option<T>>;

    /// Check if the collection contains an element.
    fn contains(&self, item: &T) -> bool;
}

/// A trait for data structures that support iteration.
pub trait Iterable<T> {
    type Iterator<'a>: Iterator<Item = &'a T>
    where
        Self: 'a,
        T: 'a;

    /// Get an iterator over the structure.
    fn iter(&self) -> Self::Iterator<'_>;
}

/// A trait for spatial data structures.
pub trait Spatial<P, T> {
    /// Insert an item at a specific position.
    fn insert(&mut self, position: P, item: T) -> Result<()>;

    /// Find items within a specified range.
    fn query_range(&self, range: &impl RangeQuery<P>) -> Vec<&T>;

    /// Find the nearest neighbors to a position.
    fn nearest_neighbors(&self, position: &P, k: usize) -> Vec<&T>;
}

/// A trait for range queries in spatial data structures.
pub trait RangeQuery<P> {
    /// Check if a position is within the range.
    fn contains(&self, position: &P) -> bool;
}

/// The main trait that all bitwise data structures must implement.
pub trait BitwiseStructure {
    /// Returns the size of the structure in bits.
    fn bit_size(&self) -> usize;

    /// Sets a bit at the specified index.
    fn set_bit(&mut self, index: usize) -> Result<()>;

    /// Clears a bit at the specified index.
    fn clear_bit(&mut self, index: usize) -> Result<()>;

    /// Gets the value of a bit at the specified index.
    fn get_bit(&self, index: usize) -> bool;

    /// Toggles a bit at the specified index.
    fn toggle_bit(&mut self, index: usize) -> Result<()>;

    /// Returns the number of set bits (1s) in the structure.
    fn count_ones(&self) -> usize;

    /// Returns the number of cleared bits (0s) in the structure.
    fn count_zeros(&self) -> usize {
        self.bit_size() - self.count_ones()
    }

    /// Returns the density (ratio of set bits to total bits) of the structure.
    fn density(&self) -> f64 {
        if self.bit_size() == 0 {
            return 0.0;
        }
        self.count_ones() as f64 / self.bit_size() as f64
    }
}

/// Trait for structures that support bit range operations.
pub trait RangeOperations {
    /// Sets all bits in the specified range [start, end).
    fn set_range(&mut self, start: usize, end: usize) -> Result<()>;

    /// Clears all bits in the specified range [start, end).
    fn clear_range(&mut self, start: usize, end: usize) -> Result<()>;

    /// Toggles all bits in the specified range [start, end).
    fn toggle_range(&mut self, start: usize, end: usize) -> Result<()>;

    /// Returns true if any bit is set in the specified range [start, end).
    fn any_in_range(&self, start: usize, end: usize) -> bool;

    /// Returns true if all bits are set in the specified range [start, end).
    fn all_in_range(&self, start: usize, end: usize) -> bool;

    /// Returns the number of set bits in the specified range [start, end).
    fn count_ones_in_range(&self, start: usize, end: usize) -> usize;
}

/// Trait for structures that support rank and select operations.
pub trait RankSelect {
    /// Returns the number of set bits in the range [0, index).
    fn rank(&self, index: usize) -> usize;

    /// Returns the position of the n-th set bit (0-indexed).
    fn select(&self, n: usize) -> Option<usize>;

    /// Returns the position of the n-th cleared bit (0-indexed).
    fn select_zero(&self, n: usize) -> Option<usize>;
}

/// Trait for structures that support run-length encoding.
pub trait RunEncoding {
    /// Returns the run-length encoding of the bit structure.
    /// Each element in the result is a tuple (bit, length).
    fn runs(&self) -> Vec<(bool, usize)>;

    /// Returns the length of the longest run of set bits.
    fn longest_run_ones(&self) -> usize;

    /// Returns the length of the longest run of cleared bits.
    fn longest_run_zeros(&self) -> usize;

    /// Returns the total number of runs (consecutive sequences of the same bit).
    fn num_runs(&self) -> usize;
}

/// Trait for structures that support operations on bit slices.
pub trait BitSliceOperations {
    /// Returns a view of a subset of bits from the structure.
    fn slice(&self, start: usize, end: usize) -> Result<&[u64]>;

    /// Returns a mutable view of a subset of bits from the structure.
    fn slice_mut(&mut self, start: usize, end: usize) -> Result<&mut [u64]>;

    /// Copies a slice of bits from source to destination.
    fn copy_slice(&mut self, src_start: usize, dst_start: usize, len: usize) -> Result<()>;

    /// Shifts all bits left by a specified number of positions.
    fn shift_left(&mut self, shift: usize) -> Result<()>;

    /// Shifts all bits right by a specified number of positions.
    fn shift_right(&mut self, shift: usize) -> Result<()>;

    /// Rotates all bits left by a specified number of positions.
    fn rotate_left(&mut self, rotate: usize) -> Result<()>;

    /// Rotates all bits right by a specified number of positions.
    fn rotate_right(&mut self, rotate: usize) -> Result<()>;
}

/// Trait for efficient serialization of bit structures.
pub trait BitSerialization {
    /// Serializes the structure to a byte vector.
    fn to_bytes(&self) -> Vec<u8>;

    /// Deserializes a structure from a byte slice.
    fn from_bytes(bytes: &[u8]) -> Result<Self>
    where
        Self: Sized;

    /// Serializes the structure to a compressed byte vector.
    fn to_compressed_bytes(&self) -> Vec<u8>;

    /// Deserializes a structure from a compressed byte slice.
    fn from_compressed_bytes(bytes: &[u8]) -> Result<Self>
    where
        Self: Sized;
}

/// Trait for structures that support bit vector manipulation.
pub trait BitVectorOperations {
    /// Appends another bit structure to the end of this one.
    fn append(&mut self, other: &Self) -> Result<()>;

    /// Inserts a bit at the specified position.
    fn insert(&mut self, index: usize, value: bool) -> Result<()>;

    /// Removes a bit at the specified position.
    fn remove(&mut self, index: usize) -> Result<bool>;

    /// Swaps two bits at the specified positions.
    fn swap_bits(&mut self, index1: usize, index2: usize) -> Result<()>;

    /// Reverses the order of all bits in the structure.
    fn reverse(&mut self);

    /// Returns a new structure with reversed bit order.
    fn reversed(&self) -> Self
    where
        Self: Sized;
}

/// Trait for structures that can perform pop count operations efficiently.
pub trait PopCount {
    /// Returns the population count (number of set bits) using a fast algorithm.
    fn popcnt(&self) -> usize;

    /// Returns the parity of the structure (1 if odd number of bits set, 0 if even).
    fn parity(&self) -> bool {
        self.popcnt() % 2 == 1
    }

    /// Returns the Hamming weight of the structure (same as population count).
    fn hamming_weight(&self) -> usize {
        self.popcnt()
    }

    /// Returns the Hamming distance between this structure and another.
    fn hamming_distance(&self, other: &Self) -> Result<usize>;
}

/// Trait for structures that can serve as binary masks.
pub trait Mask<T> {
    /// Applies the bit mask to a value.
    fn apply(&self, value: &T) -> T;

    /// Creates a mask with specific bits set.
    fn with_bits(indices: &[usize]) -> Self
    where
        Self: Sized;

    /// Creates a mask with a range of bits set.
    fn with_range(start: usize, end: usize) -> Self
    where
        Self: Sized;
}

// TODO: Add more traits as needed for specific behavior patterns
