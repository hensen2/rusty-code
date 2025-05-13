//! Bitmap implementation.
//!
//! File: rusty-code/src/structures/bitwise/bitmap.rs

use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitOr, BitXor, Not};

use crate::errors::{Error, Result};
use crate::traits::{BitwiseStructure, DataStructure};

/// A bitmap implementation.
///
/// A bitmap (or bit array) is a mapping from some domain to bits,
/// where each bit represents the presence or absence of an element.
/// This implementation is optimized for space efficiency and provides
/// fast set operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bitmap {
    // TODO: Implement Bitmap fields
    bits: Vec<u64>,
    size: usize, // Size in bits
}

impl Bitmap {
    /// Creates a new bitmap with a specified size in bits.
    ///
    /// # Examples
    ///
    /// ```
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let bmap = Bitmap::new(1024);
    /// ```
    pub fn new(size: usize) -> Self {
        // Each u64 can store 64 bits, so we need (size + 63) / 64 elements
        let num_blocks = (size + 63) / 64;
        Bitmap {
            bits: vec![0; num_blocks],
            size,
        }
    }

    /// Creates a new bitmap from a slice of indices to set.
    ///
    /// # Examples
    ///
    /// ```
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let indices = vec![0, 2, 4, 6, 8];
    /// let bmap = Bitmap::from_indices(10, &indices);
    /// ```
    pub fn from_indices(size: usize, indices: &[usize]) -> Result<Self> {
        let mut bitmap = Self::new(size);
        for &idx in indices {
            if idx >= size {
                return Err(Error::InvalidKey(format!(
                    "Index {} out of bounds for bitmap of size {}",
                    idx, size
                )));
            }
            bitmap.set(idx)?;
        }
        Ok(bitmap)
    }

    /// Returns the size of the bitmap in bits.
    pub fn bit_size(&self) -> usize {
        self.size
    }

    /// Sets a bit at the specified index.
    ///
    /// # Examples
    ///
    /// ```
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let mut bmap = Bitmap::new(10);
    /// bmap.set(5);
    /// assert!(bmap.get(5));
    /// ```
    pub fn set(&mut self, index: usize) -> Result<()> {
        // TODO: Implement set
        if index >= self.size {
            return Err(Error::InvalidKey(format!(
                "Index {} out of bounds for bitmap of size {}",
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
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let mut bmap = Bitmap::new(10);
    /// bmap.set(5);
    /// bmap.clear_bit(5);
    /// assert!(!bmap.get(5));
    /// ```
    pub fn clear_bit(&mut self, index: usize) -> Result<()> {
        // TODO: Implement clear_bit
        if index >= self.size {
            return Err(Error::InvalidKey(format!(
                "Index {} out of bounds for bitmap of size {}",
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
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let mut bmap = Bitmap::new(10);
    /// bmap.toggle(5);
    /// assert!(bmap.get(5));
    /// bmap.toggle(5);
    /// assert!(!bmap.get(5));
    /// ```
    pub fn toggle(&mut self, index: usize) -> Result<()> {
        // TODO: Implement toggle
        if index >= self.size {
            return Err(Error::InvalidKey(format!(
                "Index {} out of bounds for bitmap of size {}",
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
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let mut bmap = Bitmap::new(10);
    /// bmap.set(5);
    /// assert!(bmap.get(5));
    /// assert!(!bmap.get(4));
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

    /// Returns the number of set bits (1s) in the bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let mut bmap = Bitmap::new(10);
    /// bmap.set(1);
    /// bmap.set(3);
    /// bmap.set(5);
    /// assert_eq!(bmap.count_ones(), 3);
    /// ```
    pub fn count_ones(&self) -> usize {
        // TODO: Implement count_ones
        self.bits
            .iter()
            .map(|block| block.count_ones() as usize)
            .sum()
    }

    /// Returns the number of cleared bits (0s) in the bitmap.
    pub fn count_zeros(&self) -> usize {
        self.size - self.count_ones()
    }

    /// Performs a bitwise AND operation with another bitmap.
    ///
    /// # Examples
    ///
    /// ```
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let mut bmap1 = Bitmap::new(10);
    /// bmap1.set(1);
    /// bmap1.set(3);
    /// bmap1.set(5);
    ///
    /// let mut bmap2 = Bitmap::new(10);
    /// bmap2.set(1);
    /// bmap2.set(2);
    /// bmap2.set(5);
    ///
    /// let result = bmap1.and(&bmap2);
    /// assert!(result.get(1));
    /// assert!(!result.get(2));
    /// assert!(!result.get(3));
    /// assert!(result.get(5));
    /// ```
    pub fn and(&self, other: &Self) -> Self {
        // TODO: Implement and
        let mut result = self.clone();

        for (i, block) in self.bits.iter().enumerate() {
            if i < other.bits.len() {
                result.bits[i] = *block & other.bits[i];
            } else {
                result.bits[i] = 0;
            }
        }

        result
    }

    /// Performs a bitwise OR operation with another bitmap.
    pub fn or(&self, other: &Self) -> Self {
        // TODO: Implement or
        let mut result = self.clone();

        for (i, block) in other.bits.iter().enumerate() {
            if i < result.bits.len() {
                result.bits[i] |= *block;
            }
        }

        result
    }

    /// Performs a bitwise XOR operation with another bitmap.
    pub fn xor(&self, other: &Self) -> Self {
        // TODO: Implement xor
        let mut result = self.clone();

        for (i, block) in other.bits.iter().enumerate() {
            if i < result.bits.len() {
                result.bits[i] ^= *block;
            }
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

        // Clear bits that are beyond the bitmap size
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
    /// use rusty_code::structures::bitwise::Bitmap;
    ///
    /// let mut bmap = Bitmap::new(10);
    /// bmap.set(1);
    /// bmap.set(3);
    /// bmap.set(5);
    ///
    /// let indices = bmap.to_indices();
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

    /// Compacts the bitmap by removing trailing zeros.
    pub fn compact(&mut self) {
        // Find the highest set bit
        if let Some(highest_bit) = self.to_indices().into_iter().max() {
            let new_size = highest_bit + 1;
            let new_num_blocks = (new_size + 63) / 64;
            self.bits.truncate(new_num_blocks);
            self.size = new_size;
        } else {
            // No bits are set, so compact to a single empty block
            self.bits = vec![0];
            self.size = 1;
        }
    }
}

impl DataStructure for Bitmap {
    fn name(&self) -> &str {
        "Bitmap"
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

impl BitwiseStructure for Bitmap {
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

impl BitAnd for &Bitmap {
    type Output = Bitmap;

    fn bitand(self, rhs: Self) -> Self::Output {
        self.and(rhs)
    }
}

impl BitOr for &Bitmap {
    type Output = Bitmap;

    fn bitor(self, rhs: Self) -> Self::Output {
        self.or(rhs)
    }
}

impl BitXor for &Bitmap {
    type Output = Bitmap;

    fn bitxor(self, rhs: Self) -> Self::Output {
        self.xor(rhs)
    }
}

impl Not for &Bitmap {
    type Output = Bitmap;

    fn not(self) -> Self::Output {
        self.not()
    }
}

impl Display for Bitmap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        let indices = self.to_indices();
        for (i, idx) in indices.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", idx)?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_bitmap() {
        let bmap = Bitmap::new(128);
        assert_eq!(bmap.bit_size(), 128);
        assert_eq!(bmap.count_ones(), 0);
    }

    #[test]
    fn test_set_get() {
        let mut bmap = Bitmap::new(128);
        assert!(bmap.set(64).is_ok());
        assert!(bmap.get(64));
        assert!(!bmap.get(63));
    }

    #[test]
    fn test_bitwise_ops() {
        let mut bmap1 = Bitmap::new(128);
        bmap1.set(1).unwrap();
        bmap1.set(3).unwrap();
        bmap1.set(5).unwrap();

        let mut bmap2 = Bitmap::new(128);
        bmap2.set(1).unwrap();
        bmap2.set(2).unwrap();
        bmap2.set(5).unwrap();

        let and_result = bmap1.and(&bmap2);
        assert!(and_result.get(1));
        assert!(!and_result.get(2));
        assert!(!and_result.get(3));
        assert!(and_result.get(5));

        let or_result = bmap1.or(&bmap2);
        assert!(or_result.get(1));
        assert!(or_result.get(2));
        assert!(or_result.get(3));
        assert!(or_result.get(5));
    }

    #[test]
    fn test_from_indices() {
        let indices = vec![1, 3, 5, 7, 9];
        let bmap = Bitmap::from_indices(10, &indices).unwrap();
        assert!(bmap.get(1));
        assert!(bmap.get(3));
        assert!(bmap.get(5));
        assert!(bmap.get(7));
        assert!(bmap.get(9));
        assert!(!bmap.get(0));
        assert!(!bmap.get(2));
        assert_eq!(bmap.count_ones(), 5);
    }

    // TODO: Add more tests
}
