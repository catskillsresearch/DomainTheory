module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (5.5)–(5.7).** Disjoint pairing on sets. -/
def squarePair (x y : Pomega) : Pomega :=
  {k | (∃ n ∈ x, k = 2 * n) ∨ (∃ m ∈ y, k = 2 * m + 1)}

end DomainTheory.DataTypesAsLattices
