/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import DomainTheory.ContinuousLattice.WayBelow.Basic
import DomainTheory.ContinuousLattice.WayBelow.bot_wayBelow
import DomainTheory.ContinuousLattice.WayBelow.IsContinuousLatticeu2esSup_wayBelow
import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]





/-- A strengthening of `exists_wayBelow_subset`: the witness `a ≪ z` can be taken with the whole
principal up-set `Set.Ici a` (not merely `↟a`) inside `U`. The element `a` produced lies in the
open `U`, which is upper, so `↑a ⊆ U`. -/
theorem exists_wayBelow_Ici_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ Set.Ici a ⊆ U := by
  have hne : {a | a ≪ z}.Nonempty := ⟨⊥, bot_wayBelow z⟩
  have hsup : sSup {a | a ≪ z} ∈ U := by rw [hD.sSup_wayBelow z]; exact hz
  obtain ⟨a, haz, haU⟩ := hU.2 hne (directedOn_wayBelow z) hsup
  exact ⟨a, haz, fun w hw => hU.1 (Set.mem_Ici.1 hw) haU⟩

end DomainTheory.ContinuousLattice
