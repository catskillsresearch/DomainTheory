/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise318
import DomainTheory.Neighborhood.Exercise319Sum.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
variable {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}










/-- **Exercise 3.19(iv) (Scott 1981, PRG-19).** `out₁ ∘ (f + g) ∘ in₁ = g`. -/
theorem outMap₁_comp_sumMap_comp_inMap₁ (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    (outMap₁ (h₀ := h₀') (h₁ := h₁')).comp
      ((sumMap (h₀ := h₀) (h₁ := h₁) (h₀' := h₀') (h₁' := h₁') f g).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁))) = g := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W', ⟨W, ⟨hY, _, hinj⟩, hWmem, _, hd⟩, _, hZ, hright⟩
    rcases hd with rfl | ⟨X₀, Y', hWX₀, rfl, hf⟩ | ⟨Y₀, Y', hWY₀, rfl, hg⟩
    · rw [rightPart_sumMaster] at hright
      have : Z = V₁'.master := Set.Subset.antisymm (V₁'.sub_master hZ) hright
      subst this
      exact g.mono g.master_rel (V₁.sub_master hY) subset_rfl hY V₁'.master_mem
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX₀ ▸ hinj)).elim
    · rw [rightPart_inj₁] at hright
      have hYY₀ : Y ⊆ Y₀ := inj₁_subset_inj₁.mp (hWY₀ ▸ hinj)
      exact g.mono hg hYY₀ hright hY hZ
  · intro hg
    refine ⟨inj₁ Z, ⟨inj₁ Y, ⟨g.rel_dom hg, ?_, subset_rfl⟩, ?_, ?_, ?_⟩, ?_, g.rel_cod hg, ?_⟩
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, g.rel_dom hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact Or.inr (Or.inr ⟨Y, Z, rfl, rfl, hg⟩)
    · exact Or.inr (Or.inr ⟨Z, g.rel_cod hg, rfl⟩)
    · exact (rightPart_inj₁ V₁' Z).subset

end DomainTheory.Neighborhood
