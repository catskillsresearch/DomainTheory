module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def squareFst (u : Pomega) : Pomega :=
  {n | 2 * n ∈ u}

end DomainTheory.DataTypesAsLattices
