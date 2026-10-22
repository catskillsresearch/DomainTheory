/-ai
A natural number belongs to the entries of a list if and only if it belongs to the list.

The two sides are the same by definition of the set of entries.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.entries

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

@[simp] theorem mem_entries {n : ℕ} {ns : List ℕ} : n ∈ entries ns ↔ n ∈ ns := Iff.rfl

end DomainTheory.NeighbourhoodSystems.Exercise514
