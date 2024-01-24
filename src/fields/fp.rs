// Fiat-crypto generates some unused type aliases, but we don't want to edit the generated code at all.
#![allow(dead_code)]

use cfg_if::cfg_if;

#[cfg(feature = "arkworks")]
pub mod arkworks;
pub mod u32;
pub mod u64;

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
