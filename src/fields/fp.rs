// Fiat-crypto generates some unused type aliases, but we don't want to edit the generated code at all.
#![allow(dead_code)]

use cfg_if::cfg_if;

pub mod arkworks;
pub mod u32;
pub mod u64;

#[cfg(all(not(feature = "u32_backend"), not(feature = "u64_backend")))]
compile_error!("No backend selected. Please select either: 'u32_backend' or 'u64_backend'.");
#[cfg(all(feature = "u32", feature = "u64"))]
compile_error!(
    "Multiple backends selected. Please select only one: 'u32_backend' or 'u64_backend'."
);

cfg_if! {
    if #[cfg(feature = "u32_backend")] {
        pub type Fp = u32::Fp;

        pub mod arkworks_constants {
            pub use super::u32::arkworks_constants::*;
        }
    } else {
        pub type Fp = u64::Fp;

        pub mod arkworks_constants {
            pub use super::u64::arkworks_constants::*;
        }
    }
}
