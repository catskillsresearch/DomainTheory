/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise425

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- The tail `tail n = {1ᵐ ∣ m ≥ n} = {m ∣ n ≤ m}` (the partial information "at least `n` ones"). -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

end DomainTheory.NeighbourhoodSystems.Exercise425
