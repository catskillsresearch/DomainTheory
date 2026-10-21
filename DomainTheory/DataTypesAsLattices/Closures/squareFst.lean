/-ai
The first projection of a disjoint pairing is the set of numbers whose doubles lie in the paired set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}

end DomainTheory.DataTypesAsLattices
