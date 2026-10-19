//! Counts source lines by language and scores functions by CRAP.
//!
//! The binary is the supported interface; this library exposes the same parts
//! so they can be tested on their own.

pub mod complexity;
pub mod count;
pub mod crap;
pub mod diff;
pub mod lang;
pub mod lcov;
pub mod report;
pub mod walk;
