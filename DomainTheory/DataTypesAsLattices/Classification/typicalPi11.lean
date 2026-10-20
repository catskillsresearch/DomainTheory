module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalPi11 : Set Pomega :=
  {u | ∀ y, ∃ z, funOf (funOf u y) z = ofNat 0}

end DomainTheory.DataTypesAsLattices
