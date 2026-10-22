module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Pomega

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, after (2.2).** `⊥ = ∅`. -/
def botElem : Pomega := ∅

end DomainTheory.DataTypesAsLattices
