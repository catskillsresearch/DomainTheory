/-ai
The graph of a map f is the set of codes that equal the tag of some finite list together with an output belonging to f of the set of entries of that list.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.entries
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.mem_entries

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

/-- `graph(f)` — the code of the function `f`. -/
def Graph (f : Set ℕ → Set ℕ) : Set ℕ :=
  {c | ∃ ns m, c = tag ns m ∧ m ∈ f (entries ns)}

end DomainTheory.NeighbourhoodSystems.Exercise514
