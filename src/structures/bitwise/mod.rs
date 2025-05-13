//! Bit-level data structures.
//!
//! File: rusty-code/src/structures/bitwise/mod.rs

pub mod bitmap;
// pub mod bitset;
pub mod bitvec;
// pub mod roaring;
// pub mod succinct;

// Re-export commonly used bitwise data structures
pub use self::bitmap::Bitmap;
// pub use self::bitset::BitSet;
pub use self::bitvec::BitVec;
// pub use self::roaring::RoaringBitmap;
// pub use self::succinct::SuccinctVector;
