/-ai
A set of elements of Pω is Π¹₁ when some Scott-continuous map h cuts it out by the condition that for every y there exists z such that the function coded by h(x), applied to y and then to z, returns zero.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def IsPi11 (U : Set Pomega) : Prop :=
  ∃ h, IsScottContinuous h ∧
    U = {x | ∀ y, ∃ z, funOf (funOf (h x) y) z = ofNat 0}

end DomainTheory.DataTypesAsLattices
