module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def squarePair (x y : Pomega) : Pomega :=
  {k | (∃ n ∈ x, k = 2 * n) ∨ (∃ m ∈ y, k = 2 * m + 1)}

end DomainTheory.DataTypesAsLattices
