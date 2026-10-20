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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Ico0_inj
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.aRel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- `aRel` unwound at concrete endpoints: exactly Scott's displayed condition. -/
theorem aRel_iff {r s : ℚ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    aRel (Set.Ico (0 : ℚ) r) (Set.Ico (0 : ℚ) s) ↔ (r < s ∨ (r = 1 ∧ s = 1)) := by
  constructor
  · rintro ⟨r', s', hr0', hr1', hs0', hs1', hXr, hXs, hcond⟩
    rw [Ico0_inj hr0 hr0' hXr, Ico0_inj hs0 hs0' hXs]
    exact hcond
  · intro h
    exact ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, h⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
