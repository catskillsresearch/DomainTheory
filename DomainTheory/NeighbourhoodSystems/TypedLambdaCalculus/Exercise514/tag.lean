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
