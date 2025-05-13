//! Configuration settings for the library.
//!
//! File: rusty-code/src/config.rs

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

/// Global configuration for the library.
#[derive(Clone, Debug)]
pub struct Configuration {
    /// Whether the library has been initialized.
    initialized: Arc<AtomicBool>,
    /// Maximum number of threads to use for parallel operations.
    max_threads: usize,
    /// Default capacity for data structures.
    default_capacity: usize,
    /// Whether to enable thread safety for data structures.
    thread_safe: bool,
}

impl Default for Configuration {
    fn default() -> Self {
        Self {
            initialized: Arc::new(AtomicBool::new(true)),
            max_threads: num_cpus::get(),
            default_capacity: 16,
            thread_safe: true,
        }
    }
}

impl Configuration {
    /// Create a new configuration with custom settings.
    pub fn new(max_threads: usize, default_capacity: usize, thread_safe: bool) -> Self {
        Self {
            initialized: Arc::new(AtomicBool::new(true)),
            max_threads,
            default_capacity,
            thread_safe,
        }
    }

    /// Check if the library has been initialized.
    pub fn is_initialized(&self) -> bool {
        self.initialized.load(Ordering::Relaxed)
    }

    /// Get the maximum number of threads.
    pub fn max_threads(&self) -> usize {
        self.max_threads
    }

    /// Set the maximum number of threads.
    pub fn set_max_threads(&mut self, max_threads: usize) {
        self.max_threads = max_threads;
    }

    /// Get the default capacity.
    pub fn default_capacity(&self) -> usize {
        self.default_capacity
    }

    /// Set the default capacity.
    pub fn set_default_capacity(&mut self, default_capacity: usize) {
        self.default_capacity = default_capacity;
    }

    /// Check if thread safety is enabled.
    pub fn is_thread_safe(&self) -> bool {
        self.thread_safe
    }

    /// Set thread safety.
    pub fn set_thread_safe(&mut self, thread_safe: bool) {
        self.thread_safe = thread_safe;
    }
}

// TODO: Add more configuration options as needed
