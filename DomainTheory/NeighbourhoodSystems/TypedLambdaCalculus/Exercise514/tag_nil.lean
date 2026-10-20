module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

@[simp] theorem tag_nil (m : ℕ) : tag [] m = num 0 m := rfl

end DomainTheory.NeighbourhoodSystems.Exercise514
