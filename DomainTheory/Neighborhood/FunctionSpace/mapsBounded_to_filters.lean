/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise127
import DomainTheory.Neighborhood.FunctionSpace.Basic
import DomainTheory.Neighborhood.FunctionSpace.toFilter_le_iff


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}















































theorem mapsBounded_to_filters {F : Set (ApproximableMap V₀ V₁)} (h : MapsBounded F) :
    (funSpace V₀ V₁).Bounded (Set.image toFilter F) := by
  obtain ⟨h, hh⟩ := h
  refine ⟨toFilter h, fun φ hφ => ?_⟩
  obtain ⟨f, hf, rfl⟩ := hφ
  exact (toFilter_le_iff).mpr (hh f hf)

end DomainTheory.Neighborhood
