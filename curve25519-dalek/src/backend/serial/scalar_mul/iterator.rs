//! Collect values obtained by borrowing the items yielded by an iterator.
#[cfg(verus_keep_ghost)]
use crate::specs::iterator_specs::borrowed_values;
use alloc::vec::Vec;
use core::borrow::Borrow;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::{map_postcondition, IteratorSpec};

verus! {

/// Collect a mapped iterator and retain the postcondition of each call in the proof.
fn map_vec<A, R, I, F>(iter: I, f: F) -> (v: Vec<R>) where I: Iterator<Item = A>, F: FnMut(A) -> R
    requires
        iter.obeys_prophetic_iter_laws(),
        forall|k: int|
            0 <= k < iter.remaining().len() && iter.produces()[k] ==> #[trigger] f.requires(
                (iter.remaining()[k],),
            ),
    ensures
        v@.len() == iter.remaining().len(),
        forall|k: int| 0 <= k < v@.len() ==> f.ensures((iter.remaining()[k],), #[trigger] v@[k]),
        forall|k: int| 0 <= k < v@.len() ==> #[trigger] iter.produces()[k],
{
    let m = iter.map(f);
    proof {
        map_postcondition(iter, f, m);
    }
    assert(m.obeys_prophetic_iter_laws());
    let v: Vec<R> = m.collect();
    assert(v@ == m.remaining());
    assert(m.produces().all(|p: bool| p));
    assert forall|k: int| 0 <= k < v@.len() implies #[trigger] iter.produces()[k] by {
        assert(m.produces()[k]);
    }
    v
}

/// Map and collect optional items, retaining the source of each produced result.
pub(crate) fn collect_optional_map<A, R, I: Iterator<Item = A>, F: FnMut(A) -> Option<R>>(
    iter: I,
    f: F,
) -> (out: Option<Vec<R>>)
    requires
        iter.obeys_prophetic_iter_laws(),
        forall|k: int|
            0 <= k < iter.remaining().len() && iter.produces()[k] ==> #[trigger] f.requires(
                (iter.remaining()[k],),
            ),
    ensures
        out.is_some() ==> out.unwrap()@.len() == iter.remaining().len(),
        out.is_some() ==> forall|k: int|
            0 <= k < iter.remaining().len() ==> #[trigger] iter.produces()[k],
        out.is_some() ==> forall|k: int|
            0 <= k < iter.remaining().len() ==> f.ensures(
                (iter.remaining()[k],),
                Some(#[trigger] out.unwrap()@[k]),
            ),
        out.is_none() ==> exists|k: int|
            0 <= k < iter.remaining().len() && iter.produces()[k] && f.ensures(
                (#[trigger] iter.remaining()[k],),
                None,
            ),
{
    let mapped = iter.map(f);
    proof {
        map_postcondition(iter, f, mapped);
    }
    let out = mapped.collect::<Option<Vec<R>>>();
    proof {
        crate::core_assumes::axiom_collect_optional_vec(mapped, out);
        if out.is_none() {
            let k = choose|k: int|
                0 <= k < mapped.remaining().len() && mapped.produces()[k] && (
                #[trigger] mapped.remaining()[k]).is_none();
            assert(f.ensures((iter.remaining()[k],), None));
        } else {
            let v = out.unwrap();
            assert forall|k: int|
                0 <= k < iter.remaining().len() implies #[trigger] iter.produces()[k] by {
                assert(mapped.remaining()[k] == Some(v@[k]));
                assert(mapped.produces()[k]);
            }
            assert forall|k: int| 0 <= k < iter.remaining().len() implies f.ensures(
                (iter.remaining()[k],),
                Some(#[trigger] v@[k]),
            ) by {
                assert(mapped.remaining()[k] == Some(v@[k]));
                assert(mapped.produces()[k]);
            }
        }
    }
    out
}

/// The mapped results come from borrowing the corresponding items.
pub(crate) open spec fn mapped_borrows<A: Borrow<B>, B, R, F: Fn(&B) -> R>(
    items: Seq<A>,
    results: Seq<R>,
    f: F,
    values: Seq<B>,
) -> bool {
    &&& borrowed_values(items, values)
    &&& results.len() == values.len()
    &&& forall|k: int| 0 <= k < results.len() ==> f.ensures((&values[k],), #[trigger] results[k])
}

/// Each mapped result comes from a value that the corresponding borrow may return.
pub(crate) fn collect_borrowed_map<A, B, R, I, F>(iter: I, f: F) -> (out: Vec<R>) where
    A: Borrow<B>,
    I: Iterator<Item = A>,
    F: Fn(&B) -> R,

    requires
        iter.obeys_prophetic_iter_laws(),
        forall|k: int, b: B|
            0 <= k < iter.remaining().len() && iter.produces()[k] && #[trigger] call_ensures(
                Borrow::borrow,
                (&iter.remaining()[k],),
                &b,
            ) ==> f.requires((&b,)),
    ensures
        out@.len() == iter.remaining().len(),
        forall|k: int| 0 <= k < out@.len() ==> #[trigger] iter.produces()[k],
        exists|values: Seq<B>| #[trigger] mapped_borrows(iter.remaining(), out@, f, values),
{
    let func = &f;
    let mapper = |item: A| -> (result: R)
        requires
            forall|b: B| #[trigger]
                call_ensures(Borrow::borrow, (&item,), &b) ==> (*func).requires((&b,)),
        ensures
            exists|b: B| #[trigger]
                call_ensures(Borrow::borrow, (&item,), &b) && (*func).ensures((&b,), result),
        {
            let b = item.borrow();
            assert(call_ensures(Borrow::borrow, (&item,), b));
            func(b)
        };
    let out = map_vec(iter, mapper);
    proof {
        let values = Seq::new(
            out@.len(),
            |k: int|
                choose|b: B| #[trigger]
                    call_ensures(Borrow::borrow, (&iter.remaining()[k],), &b) && f.ensures(
                        (&b,),
                        out@[k],
                    ),
        );
        assert forall|k: int| 0 <= k < values.len() implies {
            &&& #[trigger] call_ensures(Borrow::borrow, (&iter.remaining()[k],), &values[k])
            &&& f.ensures((&values[k],), out@[k])
        } by {
            assert(mapper.ensures((iter.remaining()[k],), out@[k]));
        }
        assert(mapped_borrows(iter.remaining(), out@, f, values));
    }
    out
}

} // verus!
