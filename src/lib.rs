//! # RustyCode
//!
//! `rusty-code` is a library for complex and creative data structures
//! with applications in bioinformatics, finance, and other domains.
//!
//! File: rusty-code/src/lib.rs

pub mod config;
pub mod errors;
pub mod structures;
pub mod traits;
pub mod utils;

// Version info
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

// Re-export commonly used types
pub use crate::errors::{Error, Result};
pub use crate::traits::DataStructure;

/// Initializes the library with default configuration.
///
/// # Examples
///
/// ```
/// use rusty_code::init;
///
/// let config = init();
/// assert!(config.is_initialized());
/// ```
pub fn init() -> config::Configuration {
    // TODO: Initialize default configuration
    config::Configuration::default()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_initialization() {
        let config = init();
        assert!(config.is_initialized());
    }
}
