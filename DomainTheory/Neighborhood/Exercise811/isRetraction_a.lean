/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem85
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.Bounds.OrderIso
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import DomainTheory.Neighborhood.Exercise811.Basic


namespace DomainTheory.Neighborhood.Exercise811

open NeighborhoodSystem ApproximableMap















/-- **Exercise 8.11 (second part, retraction).** `a ∘ a = a`. -/
theorem isRetraction_a : IsRetraction a := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond1⟩,
      ⟨s', t, hs0', hs1', ht0, ht1, hYs', rfl, hcond2⟩⟩
    have hss' : s = s' := Ico0_inj hs0 hs0' hYs'
    subst hss'
    refine ⟨r, t, hr0, hr1, ht0, ht1, rfl, rfl, ?_⟩
    rcases hcond1 with h1 | ⟨rfl, rfl⟩
    · rcases hcond2 with h2 | ⟨rfl, rfl⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inl h1
    · rcases hcond2 with h2 | ⟨-, rfl⟩
      · exact absurd (h2.trans_le ht1) (lt_irrefl _)
      · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨r, t, hr0, hr1, ht0, ht1, rfl, rfl, hcond⟩
    rcases hcond with h | ⟨rfl, rfl⟩
    · obtain ⟨s, hrs, hst⟩ := exists_between h
      have hs0 : 0 < s := hr0.trans hrs
      have hs1 : s ≤ 1 := (hst.trans_le ht1).le
      exact ⟨Set.Ico 0 s, ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, Or.inl hrs⟩,
        ⟨s, t, hs0, hs1, ht0, ht1, rfl, rfl, Or.inl hst⟩⟩
    · exact ⟨Set.Ico 0 1, ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩,
        ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩

end DomainTheory.Neighborhood.Exercise811
