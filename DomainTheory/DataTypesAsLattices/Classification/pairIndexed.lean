
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def pairIndexed (fs : ℕ → Pomega → Pomega) (x : Pomega) : Pomega :=
  {k | ∃ n m, k = pair n m ∧ m ∈ fs n x}

end DomainTheory.DataTypesAsLattices
