//! NV: narrow fixed-point verifier circuit (see results/pq-recursion-nv/DESIGN.md).
pub mod agg;
pub mod builder;
pub mod circuit;
pub mod fmt;
pub mod glue;
pub mod hash;
pub mod isa;
pub mod transcript2;
pub mod uair;
pub mod verifier;
pub mod vd;
#[cfg(test)]
mod faithful_sha_tests;
#[cfg(test)]
mod agg_tests;
#[cfg(test)]
mod hash_tests;
#[cfg(test)]
mod faithful_tr_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod prep_tests;
#[cfg(test)]
mod prep_demo;
#[cfg(test)]
mod faithful_dof;
#[cfg(test)]
mod faithful_tests;
#[cfg(test)]
mod stream_tests;
