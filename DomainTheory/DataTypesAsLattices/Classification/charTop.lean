/-ai
The top characteristic map of a set U sends an element x to the set of every index whenever some finite piece of x lies in U, and to the empty set otherwise.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import Mathlib.Data.Set.Finite.Powerset
import all Mathlib.Data.Set.Finite.Powerset
public import DomainTheory.DataTypesAsLattices.Classification.IsBooleanOpen

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace

def charTop (U : Set Pomega) (x : Pomega) : Pomega :=
  {_k | ∃ n, e n ⊆ x ∧ e n ∈ U}

end DomainTheory.DataTypesAsLattices
