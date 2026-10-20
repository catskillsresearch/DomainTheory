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




















/-- `bx` on a partial element: `b(σ⊥) = (bσ)⊥`. -/
theorem consMap_strBot (b : Bool) (σ : Str) :
    (consMap b).toElementMap (strBot σ) = strBot (b :: σ) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X', ⟨_, hXX'⟩, _, hY, hsub⟩
    refine ⟨hY, ?_⟩
    have hpre : prepend [b] (cone σ) ⊆ Y := (prepend_mono [b] hXX').trans hsub
    rwa [prepend_cone] at hpre
  · rintro ⟨hY, hsub⟩
    refine ⟨cone σ, ⟨memC_cone σ, subset_rfl⟩, memC_cone σ, hY, ?_⟩
    rw [prepend_cone]; exact hsub

end DomainTheory.Neighborhood.Example44
