use vstd::prelude::*;
use vstd::calc;

use vstd::arithmetic::mul::*;


verus! {


        struct Scalar52 {
            // ADAPTED CODE LINE: we give a name to the field: "limbs"
            pub limbs: [u64; 5],
        }

        #[verifier::allow_in_spec]
        fn m(x: u64, y: u64) -> (z: u128)
        requires
            x < (1u64 << 52),
            y < (1u64 << 52),
        ensures
            z < (1u128 << 104),
        returns (x * y) as u128
        {
            proof {
                assert(1u128 << 52 == 1u64 << 52) by (bit_vector);
                assert((x as u128) < (1u128 << 52));
                assert((y as u128) < (1u128 << 52));
                calc! {
                    (<)
                    (x as u128) * (y as u128); (<=) {
                        if x > 0 {
                            lemma_mul_strict_inequality(y as int, (1u128 << 52) as int, x as int);
                        } else {
                            assert(x == 0);
                            assert((x as u128) * (y as u128) == 0);
                            assert((x as u128) * (1u128 << 52) == 0);
                        }
                    }
                    (x as u128) * (1u128 << 52); (<) {
                        lemma_mul_strict_inequality(x as int, (1u128 << 52) as int, (1u128 << 52) as int);
                    }
                    (1u128 << 52) * (1u128 << 52);
                }
                assert((1u128 << 52) * (1u128 << 52) == (1u128 << 104)) by (compute);
            }
            (x as u128) * (y as u128)
        }

    fn square_internal(a: &Scalar52) -> (res: [u128; 9])
    requires
        forall|i: int| 0 <= i < 5 ==> a.limbs[i] < (1u64 << 52),
    {
        let mut z = [0u128; 9];

        z[0] = m(a.limbs[0], a.limbs[0]);
        proof!{
            assert (a.limbs[0] < (1u64 << 52));
            assert (a.limbs[1] < (1u64 << 52));
            let x = a.limbs[0];
            let y = a.limbs[1];
            assert (x < (1u64 << 52));
            assert (y < (1u64 << 52));
            assert (m(x, y) < (1u128 << 104));
            assume (m(a.limbs[0], a.limbs[1]) < (1u128 << 104));
            assume (2 * m(a.limbs[0], a.limbs[1]) < (2u128 << 104));
            assert( m(3, 3) < 10 );
        }
        z[1] = m(a.limbs[0], a.limbs[1]) * 2;

        z
    }
}

fn main()
{}
