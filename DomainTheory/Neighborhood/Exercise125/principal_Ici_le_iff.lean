/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic
import DomainTheory.Neighborhood.Exercise125.Basic


namespace DomainTheory.Neighborhood

namespace FinalSegment

open NeighborhoodSystem



variable {Δ : Type*} [LinearOrder Δ] [Nonempty Δ]




/-- The principal finite elements `↑(Ici a)`; the correspondence `a ↦ ↑(Ici a)` is
order-*reversing* (`Ici a ⊆ Ici b ↔ b ≤ a`), one of Scott's "finite elements". -/
theorem principal_Ici_le_iff (a b : Δ) :
    (finalSegmentSystem Δ).principal (Ici_mem a) ≤ (finalSegmentSystem Δ).principal (Ici_mem b)
      ↔ a ≤ b := by
  rw [NeighborhoodSystem.principal_le_iff, Set.Ici_subset_Ici]

end FinalSegment
end DomainTheory.Neighborhood
