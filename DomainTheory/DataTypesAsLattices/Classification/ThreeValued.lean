module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

class ThreeValued (x : Pomega) : Prop where
  out : x = botElem ∨ x = ofNat 0 ∨ x = topElem

end DomainTheory.DataTypesAsLattices
