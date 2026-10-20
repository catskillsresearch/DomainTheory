/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
import all Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
import all Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
import all Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **Exercise 8.11's `R`.** The neighbourhoods are exactly the half-open rational intervals
`[0,r)` for `0 < r ≤ 1`, nested by `r` (`Ico0_subset_or_supset`), so `ofNestedOrDisjoint` applies
directly with no disjoint case ever needed. -/
def R : NeighborhoodSystem ℚ :=
  NeighborhoodSystem.ofNestedOrDisjoint
    (mem := fun X => ∃ r : ℚ, 0 < r ∧ r ≤ 1 ∧ X = Set.Ico (0 : ℚ) r)
    (master := Set.Ico (0 : ℚ) 1)
    (master_nonempty := ⟨0, by norm_num⟩)
    (master_mem := ⟨1, one_pos, le_refl 1, rfl⟩)
    (hnd := by
      rintro X Y ⟨r, hr0, hr1, rfl⟩ ⟨s, hs0, hs1, rfl⟩
      rcases le_total r s with h | h
      · exact Or.inl (Set.Ico_subset_Ico le_rfl h)
      · exact Or.inr (Or.inl (Set.Ico_subset_Ico le_rfl h)))
    (sub_master := by
      rintro X ⟨r, hr0, hr1, rfl⟩
      exact Set.Ico_subset_Ico le_rfl hr1)

end DomainTheory.NeighbourhoodSystems.Exercise811
