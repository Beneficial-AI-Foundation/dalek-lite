pub mod core_specs;

pub mod edwards_specs;

pub mod proba_specs;

pub mod field_specs;

pub mod field_specs_u64;

pub mod montgomery_specs;

pub mod arithm_trait_specs;

pub mod primality_specs;

pub mod ristretto_specs;

#[cfg(feature = "lizard")]
pub mod lizard_specs;

pub mod iterator_specs;

#[cfg(all(feature = "alloc", verus_keep_ghost))]
pub mod multiscalar_usage_checks;

pub mod scalar_specs;

pub mod scalar52_specs;

pub mod montgomery_reduce_specs;

pub mod window_specs;
