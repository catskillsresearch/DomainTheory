/-ai
Application of a coded function sends a set u of codes and an argument set x to the set of outputs m for which some finite list, with every entry in x, has its tag with m belonging to u.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.mem_entries

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

/-- `fun(u)(x)` — apply the "function coded by `u`" to argument `x`. -/
def Fun (u : Set ℕ) (x : Set ℕ) : Set ℕ :=
  {m | ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ tag ns m ∈ u}

end DomainTheory.NeighbourhoodSystems.Exercise514
