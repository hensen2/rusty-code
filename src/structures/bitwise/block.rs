//! ============================================================================
//! BitBlock Trait and Implementations
//!
//! File: rusty-code/src/structures/bitwise/block.rs
//! //! ============================================================================

/// Trait for types that can serve as bit storage blocks (unsigned integers)
pub trait BitBlock:
    Copy
    + Eq
    + core::fmt::Debug
    + core::ops::BitAnd<Output = Self>
    + core::ops::BitOr<Output = Self>
    + core::ops::BitXor<Output = Self>
    + core::ops::Not<Output = Self>
    + core::ops::Shl<usize, Output = Self>
    + core::ops::Shr<usize, Output = Self>
{
    const BITS: usize; // Bits per block - enables efficient indexing
    const ZERO: Self; // Zero value - for initialization
    const ONE: Self; // One value - for bit masks
    const MAX: Self; // All bits set - for complement operations

    /// Count leading zeros
    fn leading_zeros(self) -> usize; // Maps to LZCNT instruction on x86

    /// Count trailing zeros  
    fn trailing_zeros(self) -> usize; // Maps to TZCNT instruction on x86  

    /// Count set bits (population count)
    fn count_ones(self) -> usize; // Maps to POPCNT instruction

    /// Get bit at position
    fn get_bit(self, pos: usize) -> bool;

    /// Set bit at position
    fn set_bit(self, pos: usize) -> Self;

    /// Clear bit at position
    fn clear_bit(self, pos: usize) -> Self;

    /// Toggle bit at position
    fn toggle_bit(self, pos: usize) -> Self;
}

/// Implementations macro for unsigned integer types
macro_rules! impl_bit_block {
    ($type:ty) => {
        impl BitBlock for $type {
            const BITS: usize = <$type>::BITS as usize;
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const MAX: Self = <$type>::MAX;

            fn leading_zeros(self) -> usize {
                self.leading_zeros() as usize
            }

            fn trailing_zeros(self) -> usize {
                self.trailing_zeros() as usize
            }

            fn count_ones(self) -> usize {
                self.count_ones() as usize
            }

            fn get_bit(self, pos: usize) -> bool {
                (self >> pos) & Self::ONE != Self::ZERO
            }

            fn set_bit(self, pos: usize) -> Self {
                self | (Self::ONE << pos)
            }

            fn clear_bit(self, pos: usize) -> Self {
                self & !(Self::ONE << pos)
            }

            fn toggle_bit(self, pos: usize) -> Self {
                self ^ (Self::ONE << pos)
            }
        }
    };
}

impl_bit_block!(u8);
impl_bit_block!(u16);
impl_bit_block!(u32);
impl_bit_block!(u64);
impl_bit_block!(u128);
impl_bit_block!(usize);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bit_block_constants() {
        assert_eq!(<u8 as BitBlock>::BITS, 8);
        assert_eq!(<u16 as BitBlock>::BITS, 16);
        assert_eq!(<u32 as BitBlock>::BITS, 32);
        assert_eq!(<u64 as BitBlock>::BITS, 64);
        assert_eq!(<u128 as BitBlock>::BITS, 128);
        assert_eq!(<usize as BitBlock>::BITS, std::mem::size_of::<usize>() * 8);

        assert_eq!(u32::ZERO, 0);
        assert_eq!(u32::ONE, 1);
        assert_eq!(<u32 as BitBlock>::MAX, u32::MAX);
    }

    #[test]
    fn test_bit_manipulation() {
        let value: u8 = 0b10110100;

        // Test bit getting
        assert_eq!(value.get_bit(0), false); // LSB
        assert_eq!(value.get_bit(1), false);
        assert_eq!(value.get_bit(2), true);
        assert_eq!(value.get_bit(3), false);
        assert_eq!(value.get_bit(4), true);
        assert_eq!(value.get_bit(5), true);
        assert_eq!(value.get_bit(6), false);
        assert_eq!(value.get_bit(7), true); // MSB

        // Test bit setting
        let set_result = value.set_bit(0);
        assert_eq!(set_result, 0b10110101);

        let set_result = value.set_bit(1);
        assert_eq!(set_result, 0b10110110);

        // Test bit clearing
        let clear_result = value.clear_bit(2);
        assert_eq!(clear_result, 0b10110000);

        // Test bit toggling
        let toggle_result = value.toggle_bit(0);
        assert_eq!(toggle_result, 0b10110101);

        let toggle_result = value.toggle_bit(2);
        assert_eq!(toggle_result, 0b10110000);
    }

    #[test]
    fn test_bit_counting() {
        let value: u16 = 0b1010110100101100;
        assert_eq!(value.count_ones(), 8);
        assert_eq!(value.leading_zeros(), 0); // Starts with 1
        assert_eq!(value.trailing_zeros(), 2); // Ends with 00
    }

    #[test]
    fn test_edge_cases() {
        // All zeros
        assert_eq!(u32::ZERO.count_ones(), 0);
        assert_eq!(u32::ZERO.leading_zeros(), 32);
        assert_eq!(u32::ZERO.trailing_zeros(), 32);

        // All ones
        assert_eq!(<u32 as BitBlock>::MAX.count_ones(), 32);
        assert_eq!(<u32 as BitBlock>::MAX.leading_zeros(), 0);
        assert_eq!(<u32 as BitBlock>::MAX.trailing_zeros(), 0);

        // Single bit
        assert_eq!(u32::ONE.count_ones(), 1);
        assert_eq!(u32::ONE.leading_zeros(), 31);
        assert_eq!(u32::ONE.trailing_zeros(), 0);
    }
}
