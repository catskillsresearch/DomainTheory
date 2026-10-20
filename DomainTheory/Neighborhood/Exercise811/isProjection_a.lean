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
import DomainTheory.Neighborhood.Exercise811.aRel_le
import DomainTheory.Neighborhood.Exercise811.isRetraction_a


namespace DomainTheory.Neighborhood.Exercise811

open NeighborhoodSystem ApproximableMap















/-- **Exercise 8.11 (second part, projection).** `a ⊑ I_R`. -/
theorem isProjection_a : IsProjection a := by
  refine ⟨isRetraction_a, ?_⟩
  rintro X Y ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond⟩
  exact ⟨⟨r, hr0, hr1, rfl⟩, ⟨s, hs0, hs1, rfl⟩, Set.Ico_subset_Ico le_rfl (aRel_le hcond)⟩

end DomainTheory.Neighborhood.Exercise811
