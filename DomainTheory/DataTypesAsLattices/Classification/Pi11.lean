module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

class Pi11 (U : Set Pomega) : Prop where
  out : ∃ h, IsScottContinuous h ∧
    U = {x | ∀ y, ∃ z, funOf (funOf (h x) y) z = ofNat 0}

end DomainTheory.DataTypesAsLattices
