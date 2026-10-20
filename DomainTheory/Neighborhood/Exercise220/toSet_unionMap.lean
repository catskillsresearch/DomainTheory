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
























theorem toSet_unionMap (x y : powerSet.Element) :
    toSet (unionMap.toElementMap₂ x y) = toSet x ∪ toSet y := by
  ext k
  simp only [mem_toSet, ApproximableMap₂.mem_toElementMap₂, Set.mem_union]
  constructor
  · rintro ⟨X, Y, hxX, hyY, _, _, _, hsub⟩
    by_cases hkX : k ∈ X
    · refine Or.inr ?_
      have hkY : k ∉ Y := fun hkY => (hsub ⟨hkX, hkY⟩) rfl
      exact y.up_mem hyY (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkY)
    · exact Or.inl (x.up_mem hxX (mem_compl_singleton k) (Set.subset_compl_singleton_iff.mpr hkX))
  · rintro (hkx | hky)
    · exact ⟨{k}ᶜ, Set.univ, hkx, y.master_mem, mem_compl_singleton k, powerSet.master_mem,
        mem_compl_singleton k, Set.inter_subset_left⟩
    · exact ⟨Set.univ, {k}ᶜ, x.master_mem, hky, powerSet.master_mem, mem_compl_singleton k,
        mem_compl_singleton k, Set.inter_subset_right⟩

end DomainTheory.Neighborhood.Exercise220
