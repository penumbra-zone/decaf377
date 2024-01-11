//! Auto-generated, formally-verified field arithmetic implementations, together
//! with wrapper types that make the generated code actually usable.
//!
//! ## Code Structure
//!
//! We have two backends (`u32` and `u64`) and three fields (`Fp`, `Fq`, and
//! `Fr`), giving six implementations total. This code is organized into submodules:
//! ```ascii,no_run
//! fields::{u32, u64}::{fp, fq, fr}::{
//!     fiat, // generated code goes here
//!     wrapper, // wrapper types Fp,Fq,Fr, putting a Rust API on the generated code
//!     arkworks, // impls of arkworks traits for the wrapper types
//! }
//! ```
//! The Fp is a 48-byte field element, while Fq and Fr are 32-byte field elements.
//! The wrapper code is all copy-pasted and should be kept in sync after any edits.
//! The different backends should have identical external interfaces, so they can be
//! used with a cfg-able type alias.

pub mod fp;
pub mod fq;
pub mod fr;
