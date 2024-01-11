#[cfg(all(not(feature = "u32"), not(feature = "u64")))]
// compile_error!("No backend selected. Please select either: 'u32_backend' or 'u64_backend'.");

#[cfg(all(feature = "u32", feature = "u64"))]
compile_error!("Multiple backends selected. Please select only one: 'u32_backend' or 'u64_backend'.");

// #[cfg(feature = "arkworks")]
pub mod arkworks;