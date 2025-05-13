//! Bit vector implementation.
//!
//! File: biocomplexity/src/structures/bitwise/bitvec.rs

use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitOr, BitXor, Index, Not};

use crate::errors::{Error, Result};
use crate::traits::{BitwiseStructure, DataStructure};

/// A bit vector implementation.
///
/// Similar to a bitmap, but offers dynamic resizing and
/// provides methods to handle it as a growable array of bits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitVec {
    // TODO: Implement BitVec fields
    bits: Vec<u64>,
    size: usize, // Size in bits
}

impl BitVec {
    /// Creates a new, empty BitVec.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let bvec = BitVec::new();
    /// ```
    pub fn new() -> Self {
        BitVec {
            bits: Vec::new(),
            size: 0,
        }
    }

    /// Creates a new BitVec with a specified size in bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let bvec = BitVec::with_capacity(1024);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        let num_blocks = (capacity + 63) / 64;
        BitVec {
            bits: vec![0; num_blocks],
            size: capacity,
        }
    }

    /// Creates a new BitVec from a slice of indices to set.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let indices = vec![0, 2, 4, 6, 8];
    /// let bvec = BitVec::from_indices(&indices);
    /// ```
    pub fn from_indices(indices: &[usize]) -> Self {
        if indices.is_empty() {
            return Self::new();
        }

        // Find the maximum index to determine size
        let max_index = *indices.iter().max().unwrap();
        let mut bitvec = Self::with_capacity(max_index + 1);

        for &idx in indices {
            bitvec.set(idx).unwrap();
        }

        bitvec
    }

    /// Returns the size of the BitVec in bits.
    pub fn bit_size(&self) -> usize {
        self.size
    }

    /// Resizes the BitVec to the specified size in bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::new();
    /// bvec.resize(1024);
    /// ```
    pub fn resize(&mut self, new_size: usize) {
        let new_num_blocks = (new_size + 63) / 64;

        if new_num_blocks <= self.bits.len() {
            // Shrinking
            self.bits.truncate(new_num_blocks);

            // Clear bits that are beyond the new size in the last block
            if new_size % 64 != 0 && !self.bits.is_empty() {
                let last_idx = self.bits.len() - 1;
                let valid_bits = new_size % 64;
                let mask = (1u64 << valid_bits) - 1;
                self.bits[last_idx] &= mask;
            }
        } else {
            // Growing
            self.bits.resize(new_num_blocks, 0);
        }

        self.size = new_size;
    }

    /// Pushes a bit to the end of the BitVec.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::new();
    /// bvec.push(true);
    /// bvec.push(false);
    /// ```
    pub fn push(&mut self, value: bool) {
        // TODO: Implement push
        let idx = self.size;
        self.resize(idx + 1);
        if value {
            self.set(idx).unwrap();
        }
    }

    /// Pops a bit from the end of the BitVec.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::new();
    /// bvec.push(true);
    /// assert_eq!(bvec.pop(), Some(true));
    /// assert_eq!(bvec.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<bool> {
        // TODO: Implement pop
        if self.size == 0 {
            return None;
        }

        let idx = self.size - 1;
        let value = self.get(idx);
        self.resize(idx);

        Some(value)
    }

    /// Sets a bit at the specified index.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::with_capacity(10);
    /// bvec.set(5);
    /// assert!(bvec.get(5));
    /// ```
    pub fn set(&mut self, index: usize) -> Result<()> {
        // TODO: Implement set
        if index >= self.size {
            return Err(Error::InvalidKey(format!(
                "Index {} out of bounds for BitVec of size {}",
                index, self.size
            )));
        }

        let block_idx = index / 64;
        let bit_idx = index % 64;
        self.bits[block_idx] |= 1u64 << bit_idx;

        Ok(())
    }

    /// Clears a bit at the specified index.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::with_capacity(10);
    /// bvec.set(5);
    /// bvec.clear_bit(5);
    /// assert!(!bvec.get(5));
    /// ```
    pub fn clear_bit(&mut self, index: usize) -> Result<()> {
        // TODO: Implement clear_bit
        if index >= self.size {
            return Err(Error::InvalidKey(format!(
                "Index {} out of bounds for BitVec of size {}",
                index, self.size
            )));
        }

        let block_idx = index / 64;
        let bit_idx = index % 64;
        self.bits[block_idx] &= !(1u64 << bit_idx);

        Ok(())
    }

    /// Toggles a bit at the specified index.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::with_capacity(10);
    /// bvec.toggle(5);
    /// assert!(bvec.get(5));
    /// bvec.toggle(5);
    /// assert!(!bvec.get(5));
    /// ```
    pub fn toggle(&mut self, index: usize) -> Result<()> {
        // TODO: Implement toggle
        if index >= self.size {
            return Err(Error::InvalidKey(format!(
                "Index {} out of bounds for BitVec of size {}",
                index, self.size
            )));
        }

        let block_idx = index / 64;
        let bit_idx = index % 64;
        self.bits[block_idx] ^= 1u64 << bit_idx;

        Ok(())
    }

    /// Gets the value of a bit at the specified index.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::with_capacity(10);
    /// bvec.set(5);
    /// assert!(bvec.get(5));
    /// assert!(!bvec.get(4));
    /// ```
    pub fn get(&self, index: usize) -> bool {
        // TODO: Implement get
        if index >= self.size {
            return false;
        }

        let block_idx = index / 64;
        let bit_idx = index % 64;
        (self.bits[block_idx] & (1u64 << bit_idx)) != 0
    }

    /// Returns the number of set bits (1s) in the BitVec.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::with_capacity(10);
    /// bvec.set(1);
    /// bvec.set(3);
    /// bvec.set(5);
    /// assert_eq!(bvec.count_ones(), 3);
    /// ```
    pub fn count_ones(&self) -> usize {
        // TODO: Implement count_ones
        self.bits
            .iter()
            .map(|block| block.count_ones() as usize)
            .sum()
    }

    /// Returns the number of cleared bits (0s) in the BitVec.
    pub fn count_zeros(&self) -> usize {
        self.size - self.count_ones()
    }

    /// Performs a bitwise AND operation with another BitVec.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec1 = BitVec::with_capacity(10);
    /// bvec1.set(1);
    /// bvec1.set(3);
    /// bvec1.set(5);
    ///
    /// let mut bvec2 = BitVec::with_capacity(10);
    /// bvec2.set(1);
    /// bvec2.set(2);
    /// bvec2.set(5);
    ///
    /// let result = bvec1.and(&bvec2);
    /// assert!(result.get(1));
    /// assert!(!result.get(2));
    /// assert!(!result.get(3));
    /// assert!(result.get(5));
    /// ```
    pub fn and(&self, other: &Self) -> Self {
        // TODO: Implement and
        let size = self.size.max(other.size);
        let mut result = Self::with_capacity(size);

        for (i, block) in self.bits.iter().enumerate() {
            if i < other.bits.len() {
                result.bits[i] = *block & other.bits[i];
            } else {
                result.bits[i] = 0;
            }
        }

        result
    }

    /// Performs a bitwise OR operation with another BitVec.
    pub fn or(&self, other: &Self) -> Self {
        // TODO: Implement or
        let size = self.size.max(other.size);
        let mut result = Self::with_capacity(size);

        for i in 0..result.bits.len() {
            let self_bit = if i < self.bits.len() { self.bits[i] } else { 0 };
            let other_bit = if i < other.bits.len() {
                other.bits[i]
            } else {
                0
            };
            result.bits[i] = self_bit | other_bit;
        }

        result
    }

    /// Performs a bitwise XOR operation with another BitVec.
    pub fn xor(&self, other: &Self) -> Self {
        // TODO: Implement xor
        let size = self.size.max(other.size);
        let mut result = Self::with_capacity(size);

        for i in 0..result.bits.len() {
            let self_bit = if i < self.bits.len() { self.bits[i] } else { 0 };
            let other_bit = if i < other.bits.len() {
                other.bits[i]
            } else {
                0
            };
            result.bits[i] = self_bit ^ other_bit;
        }

        result
    }

    /// Performs a bitwise NOT operation.
    pub fn not(&self) -> Self {
        // TODO: Implement not
        let mut result = self.clone();

        for i in 0..result.bits.len() {
            result.bits[i] = !self.bits[i];
        }

        // Clear bits that are beyond the BitVec size
        if self.size % 64 != 0 {
            let last_idx = result.bits.len() - 1;
            let valid_bits = self.size % 64;
            let mask = (1u64 << valid_bits) - 1;
            result.bits[last_idx] &= mask;
        }

        result
    }

    /// Extracts indices of all set bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use biocomplexity::structures::bitwise::BitVec;
    ///
    /// let mut bvec = BitVec::with_capacity(10);
    /// bvec.set(1);
    /// bvec.set(3);
    /// bvec.set(5);
    ///
    /// let indices = bvec.to_indices();
    /// assert_eq!(indices, vec![1, 3, 5]);
    /// ```
    pub fn to_indices(&self) -> Vec<usize> {
        // TODO: Implement to_indices
        let mut indices = Vec::with_capacity(self.count_ones());

        for i in 0..self.size {
            if self.get(i) {
                indices.push(i);
            }
        }

        indices
    }

    /// Returns an iterator over the set bits.
    pub fn iter_ones(&self) -> BitVecOnesIterator {
        BitVecOnesIterator {
            bitvec: self,
            index: 0,
        }
    }

    /// Returns a slice of the underlying storage.
    pub fn as_slice(&self) -> &[u64] {
        &self.bits
    }

    /// Returns a mutable slice of the underlying storage.
    pub fn as_slice_mut(&mut self) -> &mut [u64] {
        &mut self.bits
    }
}

/// An iterator over the set bits in a BitVec.
pub struct BitVecOnesIterator<'a> {
    bitvec: &'a BitVec,
    index: usize,
}

impl<'a> Iterator for BitVecOnesIterator<'a> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> {
        while self.index < self.bitvec.bit_size() {
            let idx = self.index;
            self.index += 1;

            if self.bitvec.get(idx) {
                return Some(idx);
            }
        }

        None
    }
}

impl DataStructure for BitVec {
    fn name(&self) -> &str {
        "BitVec"
    }

    fn size(&self) -> usize {
        self.count_ones()
    }

    fn clear(&mut self) {
        for block in &mut self.bits {
            *block = 0;
        }
    }
}

impl BitwiseStructure for BitVec {
    fn bit_size(&self) -> usize {
        self.bit_size()
    }

    fn set_bit(&mut self, index: usize) -> Result<()> {
        self.set(index)
    }

    fn clear_bit(&mut self, index: usize) -> Result<()> {
        self.clear_bit(index)
    }

    fn get_bit(&self, index: usize) -> bool {
        self.get(index)
    }

    fn toggle_bit(&mut self, index: usize) -> Result<()> {
        self.toggle(index)
    }

    fn count_ones(&self) -> usize {
        self.count_ones()
    }
}

impl Index<usize> for BitVec {
    type Output = bool;

    fn index(&self, index: usize) -> &Self::Output {
        if self.get(index) { &true } else { &false }
    }
}

impl BitAnd for &BitVec {
    type Output = BitVec;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}

impl BitOr for &BitVec {
    type Output = BitVec;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

impl BitXor for &BitVec {
    type Output = BitVec;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.xor(rhs)
    }
}

impl Not for &BitVec {
    type Output = BitVec;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl Display for BitVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for i in 0..self.size {
            write!(f, "{}", if self.get(i) { '1' } else { '0' })?;
        }
        Ok(())
    }
}

impl FromIterator<bool> for BitVec {
    fn from_iter<I: IntoIterator<Item = bool>>(iter: I) -> Self {
        let mut bitvec = BitVec::new();
        for bit in iter {
            bitvec.push(bit);
        }
        bitvec
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_bitvec() {
        let bvec = BitVec::new();
        assert_eq!(bvec.bit_size(), 0);
        assert_eq!(bvec.count_ones(), 0);
    }

    #[test]
    fn test_with_capacity() {
        let bvec = BitVec::with_capacity(128);
        assert_eq!(bvec.bit_size(), 128);
        assert_eq!(bvec.count_ones(), 0);
    }

    #[test]
    fn test_push_pop() {
        let mut bvec = BitVec::new();
        bvec.push(true);
        bvec.push(false);
        bvec.push(true);

        assert_eq!(bvec.bit_size(), 3);
        assert_eq!(bvec.count_ones(), 2);

        assert_eq!(bvec.pop(), Some(true));
        assert_eq!(bvec.pop(), Some(false));
        assert_eq!(bvec.pop(), Some(true));
        assert_eq!(bvec.pop(), None);
    }

    #[test]
    fn test_from_indices() {
        let indices = vec![1, 3, 5, 7, 9];
        let bvec = BitVec::from_indices(&indices);
        assert_eq!(bvec.bit_size(), 10);
        assert!(bvec.get(1));
        assert!(bvec.get(3));
        assert!(bvec.get(5));
        assert!(bvec.get(7));
        assert!(bvec.get(9));
        assert!(!bvec.get(0));
        assert!(!bvec.get(2));
    }

    #[test]
    fn test_bitwise_ops() {
        let mut bvec1 = BitVec::with_capacity(10);
        bvec1.set(1).unwrap();
        bvec1.set(3).unwrap();
        bvec1.set(5).unwrap();

        let mut bvec2 = BitVec::with_capacity(10);
        bvec2.set(1).unwrap();
        bvec2.set(2).unwrap();
        bvec2.set(5).unwrap();

        let and_result = bvec1.and(&bvec2);
        assert!(and_result.get(1));
        assert!(!and_result.get(2));
        assert!(!and_result.get(3));
        assert!(and_result.get(5));

        let or_result = bvec1.or(&bvec2);
        assert!(or_result.get(1));
        assert!(or_result.get(2));
        assert!(or_result.get(3));
        assert!(or_result.get(5));

        let xor_result = bvec1.xor(&bvec2);
        assert!(!xor_result.get(1));
        assert!(xor_result.get(2));
        assert!(xor_result.get(3));
        assert!(!xor_result.get(5));
    }

    #[test]
    fn test_to_indices() {
        let mut bvec = BitVec::with_capacity(10);
        bvec.set(1).unwrap();
        bvec.set(3).unwrap();
        bvec.set(5).unwrap();

        let indices = bvec.to_indices();
        assert_eq!(indices, vec![1, 3, 5]);
    }

    // TODO: Add more tests
}
