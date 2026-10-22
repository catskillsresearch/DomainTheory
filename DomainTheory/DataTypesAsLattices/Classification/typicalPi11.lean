/-ai
The typical Π₁¹ set is the set of elements u of Pω such that for every y there is a z with u(y)(z) equal to the singleton {0}.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalPi11 : Set Pomega :=
  {u | ∀ y, ∃ z, funOf (funOf u y) z = ofNat 0}

end DomainTheory.DataTypesAsLattices
