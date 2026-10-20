/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise817
import DomainTheory.Neighborhood.Proposition810b
import DomainTheory.Neighborhood.Exercise326Sum
import DomainTheory.Neighborhood.Exercise315
import DomainTheory.Neighborhood.Exercise819.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u


section General

variable {α β γ δ : Type*}

/-- **Covariant functoriality of `⊴` in `prod`'s left argument.** `A ⊴ B ⟹ prod A C ⊴ prod B C`
for any `C`: pair the given projection pair with the identity on `C`. -/
theorem prod_left_trianglelefteq {A : NeighborhoodSystem α} {B : NeighborhoodSystem β}
    (C : NeighborhoodSystem γ) (h : A ⊴ B) : prod A C ⊴ prod B C := by
  obtain ⟨D', hD'B, ⟨eAD'⟩⟩ := h
  set p : ProjPair A B := (ProjPair.ofIso eAD').comp (ProjPair.ofSubsystem hD'B) with hp
  refine trianglelefteq_of_projectionPair (paired (p.inj.comp (proj₀ A C)) (proj₁ A C))
    (paired (p.proj.comp (proj₀ B C)) (proj₁ B C)) ?_ ?_
  · apply ext_of_toElementMap
    intro z
    rw [← pair_fst_snd z]
    set x := z.fst; set y := z.snd
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_paired,
      toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair,
      toElementMap_comp, toElementMap_proj₀, fst_pair, toElementMap_proj₁, snd_pair]
    have hxx : (p.proj.comp p.inj).toElementMap x = (idMap A).toElementMap x := by
      rw [p.proj_comp_inj]
    rw [toElementMap_comp, toElementMap_idMap] at hxx
    rw [hxx]
  · rw [le_iff_toElementMap_le]
    intro z
    rw [← pair_fst_snd z]
    set x := z.fst; set y := z.snd
    rw [toElementMap_comp, toElementMap_idMap, toElementMap_paired, toElementMap_paired,
      toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁, fst_pair, snd_pair,
      toElementMap_comp, toElementMap_proj₀, fst_pair, toElementMap_proj₁, snd_pair]
    apply pair_le_pair_iff.mpr
    refine ⟨?_, le_refl y⟩
    have hxx : (p.inj.comp p.proj).toElementMap x ≤ (idMap B).toElementMap x :=
      le_iff_toElementMap_le.mp p.inj_comp_proj_le x
    rwa [toElementMap_comp, toElementMap_idMap] at hxx

end General
end DomainTheory.Neighborhood
