module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Pomega.e
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}

end DomainTheory.DataTypesAsLattices
