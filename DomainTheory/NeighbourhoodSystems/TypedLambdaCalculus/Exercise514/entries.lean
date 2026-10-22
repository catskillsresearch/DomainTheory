module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_cons

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

/-- The finite set of entries of a list, as a subset of `ℕ`. -/
def entries (ns : List ℕ) : Set ℕ := {n | n ∈ ns}

end DomainTheory.NeighbourhoodSystems.Exercise514
