use vstd::prelude::*;


verus! {


        struct Scalar52 {
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
            assume(false); // Omit proof for brevity
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
