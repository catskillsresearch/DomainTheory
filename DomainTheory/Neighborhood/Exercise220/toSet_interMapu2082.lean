/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.ApproximableExercises
import Mathlib.Data.Set.Finite.Basic
import DomainTheory.Neighborhood.Exercise220.Basic


namespace DomainTheory.Neighborhood.Exercise220

open DomainTheory.Neighborhood NeighborhoodSystem
























theorem toSet_interMap₂ (x y : powerSet.Element) :
    toSet (interMap₂.toElementMap₂ x y) = toSet x ∩ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_inter_iff]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    have hkX : k ∉ X := fun h => (hsub (Or.inl h)) rfl
    have hkY : k ∉ Y := fun h => (hsub (Or.inr h)) rfl
    exact ⟨x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX),
      y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)⟩
  · rintro ⟨hkx, hky⟩
    exact ⟨{k}ᶜ, {k}ᶜ, hkx, hky, mem_compl_singleton k, mem_compl_singleton k,
      mem_compl_singleton k, Set.union_subset subset_rfl subset_rfl⟩

end DomainTheory.Neighborhood.Exercise220
