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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_le_of_subset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- **Building an `R.Element` from an "up-set" predicate `U`.** `U` must contain `1`, be bounded
to `(0,1]`, and be upward closed within `(0,1]` — exactly Definition 1.6's filter conditions,
transported along the bijection `r ↦ [0,r)`. -/
def mkElement (U : ℚ → Prop) (hU1 : U 1) (hUpos : ∀ r, U r → 0 < r) (hUle1 : ∀ r, U r → r ≤ 1)
    (hUup : ∀ r s, U r → r ≤ s → s ≤ 1 → U s) : R.Element where
  mem X := ∃ r, U r ∧ X = Set.Ico (0 : ℚ) r
  sub := fun ⟨r, hr, hXr⟩ => ⟨r, hUpos r hr, hUle1 r hr, hXr⟩
  master_mem := ⟨1, hU1, rfl⟩
  inter_mem := by
    rintro X Y ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    rw [Ico0_inter]
    rcases le_total r s with h | h
    · exact ⟨r, hr, by rw [min_eq_left h]⟩
    · exact ⟨s, hs, by rw [min_eq_right h]⟩
  up_mem := by
    rintro X Y ⟨r, hr, rfl⟩ hY hsub
    obtain ⟨s, hs0, hs1, rfl⟩ := hY
    exact ⟨s, hUup r s hr (Ico0_le_of_subset (hUpos r hr) hsub) hs1, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
