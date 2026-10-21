/-ai
The pair-indexed packing of a sequence of maps at x is the set of codes of pairs (n, m) for which m belongs to the nth map applied to x.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def pairIndexed (fs : ℕ → Pomega → Pomega) (x : Pomega) : Pomega :=
  {k | ∃ n m, k = pair n m ∧ m ∈ fs n x}

end DomainTheory.DataTypesAsLattices
