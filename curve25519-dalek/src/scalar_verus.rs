
#![allow(unused)]

use vstd::prelude::*;



use subtle::Choice;

use subtle::ConstantTimeEq;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::backend;
use crate::constants;

verus! {


type UnpackedScalar = backend::serial::u64::scalar::Scalar52;

#[allow(clippy::derived_hash_with_manual_eq)]
#[derive(Copy, Clone, Hash)]
pub struct Scalar {
    pub bytes: [u8; 32],
}


impl Scalar {

    pub const ONE: Self = Self {
        bytes: [
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0,
        ],
    };


    pub fn invert(&self) -> Scalar {
        Scalar::ONE
    }

}

}
