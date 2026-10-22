/-ai
The tag of the empty list with output m equals the pairing of 0 with m.

This is the empty-list clause of the definition of the tag, by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

@[simp] theorem tag_nil (m : ℕ) : tag [] m = num 0 m := rfl

end DomainTheory.NeighbourhoodSystems.Exercise514
