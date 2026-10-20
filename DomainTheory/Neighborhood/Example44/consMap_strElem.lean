/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Example23
import DomainTheory.Neighborhood.Theorem41
import DomainTheory.Neighborhood.Example44.Basic


namespace DomainTheory.Neighborhood.Example44

open DomainTheory.Neighborhood NeighborhoodSystem ApproximableMap ExampleB




















/-- `bx` on a total element: `b(σ) = (bσ)` (prepend the bit to a finite sequence). -/
theorem consMap_strElem (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strElem σ) = strElem (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] {σ} ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_singleton] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨{σ}, ⟨memC_singleton σ, subset_rfl⟩, memC_singleton σ, hY, ?_⟩
    rw [prepend_singleton]; exact hsub

end DomainTheory.Neighborhood.Example44
