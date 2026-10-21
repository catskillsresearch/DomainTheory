/-ai
The tag of a finite list together with an output m is built from the pairing function. The empty list is paired as the pairing of 0 with m, and a list with head n is paired as the pairing of n + 1 with the tag of the tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

/-- `tag [n₀, …, n_{k-1}] m = [n₀+1, …, n_{k-1}+1, 0, m]`, built from the pairing function `num`. -/
def tag : List ℕ → ℕ → ℕ
  | [], m => num 0 m
  | (n :: ns), m => num (n + 1) (tag ns m)

end DomainTheory.NeighbourhoodSystems.Exercise514
