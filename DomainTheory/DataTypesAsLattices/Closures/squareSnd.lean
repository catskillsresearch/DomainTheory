module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def squareSnd (u : Pomega) : Pomega :=
  {m | 2 * m + 1 ∈ u}

end DomainTheory.DataTypesAsLattices
