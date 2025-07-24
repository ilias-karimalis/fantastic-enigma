//! A set of utility functions and proofs used throughout the project.

use vstd::prelude::*;
use vstd::set::Set;

verus! {

pub proof fn set_map_finite_preserving<A, B>(x: Set<A>, map_fn: spec_fn(A) -> B)
    requires x.finite()
    ensures x.map(map_fn).finite()
    decreases x.len()
{
    if (x.is_empty()) {
        let y = x.map(map_fn);
        assert(y == Set::<B>::empty());
    } else {
        let x_0 = x.choose();
        set_map_finite_preserving(x.remove(x_0), map_fn);
        assert(x.map(map_fn) =~= x.remove(x_0).map(map_fn).insert(map_fn(x_0)));
    }
}

/// performs XOR on boolean predicates
pub open spec fn xor(p1: bool, p2: bool) -> bool {
    (p1 || p2) && !(p1 && p2)
}

} // verus!