
#![allow(unused)]

use vstd::prelude::*;



use subtle::Choice;

use subtle::ConstantTimeEq;

#[cfg(feature = "zeroize")]
use zeroize::Zeroize;

use crate::backend;
use crate::constants;

verus! {



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
