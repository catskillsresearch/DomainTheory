/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ApproximableExercises
import DomainTheory.Neighborhood.ExampleB
import DomainTheory.Neighborhood.Exercise221.Basic


namespace DomainTheory.Neighborhood.Exercise221

open DomainTheory.Neighborhood NeighborhoodSystem ExampleB


















/-- **`⊥ ⊏ Λ`.** The undefined sequence `⊥ = ↑Δ` is strictly below the total empty sequence
`Λ = ↑{[]}`: they are distinct because `⊥` contains only `Δ`, whereas `Λ` contains `{[]} ≠ Δ`. -/
theorem bot_lt_Lambda : C.bot < Lambda := by
  refine lt_of_le_of_ne (C.bot_le _) ?_
  intro h
  have hmem : C.bot.mem ({([] : Str)} : Set Str) := by
    rw [h]; exact ⟨memC_singleton [], subset_rfl⟩
  rw [C.mem_bot, C_master] at hmem
  have h2 : ([true] : Str) ∈ ({([] : Str)} : Set Str) := by rw [hmem]; trivial
  rw [Set.mem_singleton_iff] at h2
  exact absurd h2 (by decide)

end DomainTheory.Neighborhood.Exercise221
