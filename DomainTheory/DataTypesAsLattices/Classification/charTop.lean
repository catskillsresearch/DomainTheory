module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def charTop (U : Set Pomega) (x : Pomega) : Pomega :=
  {_k | ∃ n, e n ⊆ x ∧ e n ∈ U}

end DomainTheory.DataTypesAsLattices
