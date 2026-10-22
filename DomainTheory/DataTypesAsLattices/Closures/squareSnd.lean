/-ai
The second projection of a disjoint pairing is the set of numbers whose double plus one lies in the paired set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def squareSnd (u : Pomega) : Pomega :=
  {m | 2 * m + 1 ∈ u}

end DomainTheory.DataTypesAsLattices
