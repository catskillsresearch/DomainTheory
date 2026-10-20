module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalSigma11 : Set Pomega :=
  {u | ∃ y, funOf u (ofNat 0) ⬝ y = funOf u (ofNat 1) ⬝ y}

end DomainTheory.DataTypesAsLattices
