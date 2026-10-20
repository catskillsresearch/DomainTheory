/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise319Sum
import DomainTheory.Neighborhood.Product
import DomainTheory.Neighborhood.Exercise324Distrib.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}




/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `[a, b] ∘ in₀ = a`. -/
theorem copair_comp_inMap₀ (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₀ = a := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨W, ⟨hX, _, hinj⟩, _, hZ, hd⟩
    rcases hd with rfl | ⟨X', hWX', hf⟩ | ⟨Y', hWY', hg⟩
    · exact a.rel_master hX
    · exact a.mono hf (inj₀_subset_inj₀.mp (hWX' ▸ hinj)) subset_rfl hX hZ
    · exact (not_inj₀_subset_inj₁ (h₀ X hX) (hWY' ▸ hinj)).elim
  · intro hf
    exact ⟨inj₀ X, ⟨a.rel_dom hf, Or.inr (Or.inl ⟨X, a.rel_dom hf, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inl ⟨X, a.rel_dom hf, rfl⟩), a.rel_cod hf,
      Or.inr (Or.inl ⟨X, rfl, hf⟩)⟩

end DomainTheory.Neighborhood
