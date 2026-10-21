/-ai
If the identity combinator is contained in the function space of dEq with itself, then dEq equals that function space.

One inclusion rewrites dEq by its fixed-point equation and absorbs the union by the hypothesis. The other rewrites the right-hand copy of dEq by the same equation and takes the right summand of the union.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_25

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































theorem eq_5_25_arrow (hI : Icomb ⊆ arrowR dEq dEq) :
    dEq = arrowR dEq dEq := by
  apply subset_antisymm
  · nth_rw 1 [eq_5_25]
    exact Set.union_subset hI subset_rfl
  · nth_rw 3 [eq_5_25]
    exact Set.subset_union_right

end DomainTheory.DataTypesAsLattices
