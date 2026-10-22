module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsSigma11 (U : Set Pomega) : Prop :=
  ∃ f g, IsScottContinuous f ∧ IsScottContinuous g ∧
    U = {x | ∃ y, funOf (f x) y = funOf (g x) y}

end DomainTheory.DataTypesAsLattices
