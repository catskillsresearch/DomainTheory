/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.Neighborhood.Exercise112.Basic
public import DomainTheory.Neighborhood.Exercise112.fin_le_iff

@[expose] public section


namespace DomainTheory.Neighborhood.Exercise112

open DomainTheory.Neighborhood NeighborhoodSystem












/-- The chain `fin 0 ⊏ fin 1 ⊏ ⋯` is strictly increasing. -/
theorem fin_strictMono : StrictMono fin := by
  intro n m hnm
  refine lt_of_le_of_ne ((fin_le_iff n m).mpr hnm.le) ?_
  intro heq
  have : m ≤ n := (fin_le_iff m n).mp (le_of_eq heq.symm)
  exact absurd (le_antisymm hnm.le this) (Nat.ne_of_lt hnm)

end DomainTheory.Neighborhood.Exercise112
