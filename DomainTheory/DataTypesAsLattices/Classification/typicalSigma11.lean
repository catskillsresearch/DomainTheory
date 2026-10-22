/-ai
The typical Σ₁¹ set is the set of elements u of Pω for which there is a y such that u applied to {0}, and u applied to {1}, agree when both are applied to y.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def typicalSigma11 : Set Pomega :=
  {u | ∃ y, funOf u (ofNat 0) ⬝ y = funOf u (ofNat 1) ⬝ y}

end DomainTheory.DataTypesAsLattices
