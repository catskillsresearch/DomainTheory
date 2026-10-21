/-ai
The tag of a list with head n equals the pairing of n + 1 with the tag of the tail.

This is the cons clause of the definition of the tag, by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

@[simp] theorem tag_cons (n : ℕ) (ns : List ℕ) (m : ℕ) :
    tag (n :: ns) m = num (n + 1) (tag ns m) := rfl

end DomainTheory.NeighbourhoodSystems.Exercise514
