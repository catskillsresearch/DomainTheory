/-ai
The greatest element of Pω is the set of all natural numbers. In Scott's notation after (2.2), this top element is ω.
ai-/
module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import DomainTheory.DataTypesAsLattices.Pomega.Pomega

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, after (2.2).** `⊤ = ω`. -/
def topElem : Pomega := Set.univ

end DomainTheory.DataTypesAsLattices
