//! Error types for the rusty-code library.
//!
//! File: rusty-code/src/errors.rs

use thiserror::Error;

/// A specialized Result type for rusty-code operations.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur in the rusty-code library.
#[derive(Error, Debug)]
pub enum Error {
    /// An error occurred when a structure is accessed with an invalid key or index.
    #[error("Invalid key or index: {0}")]
    InvalidKey(String),

    /// An error occurred when a structure has reached its capacity.
    #[error("Structure at capacity: {0}")]
    CapacityReached(String),

    /// An error occurred when a structure's internal state is inconsistent.
    #[error("Internal structure inconsistency: {0}")]
    InternalInconsistency(String),

    /// An error occurred with I/O operations (serialization/deserialization).
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),

    /// An error occurred during JSON serialization or deserialization.
    #[error("JSON error: {0}")]
    Json(#[from] serde_json::Error),

    /// An error that doesn't fit into other categories.
    #[error("Other error: {0}")]
    Other(String),
}

// TODO: Implement additional error conversion traits as needed
