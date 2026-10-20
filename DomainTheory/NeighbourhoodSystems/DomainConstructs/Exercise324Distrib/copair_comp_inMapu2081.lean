/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}




/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `[a, b] ∘ in₁ = b`. -/
theorem copair_comp_inMap₁ (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₁ = b := by
  apply ApproximableMap.ext
  intro Y Z
  constructor
  · rintro ⟨W, ⟨hY, _, hinj⟩, _, hZ, hd⟩
    rcases hd with rfl | ⟨X', hWX', hf⟩ | ⟨Y', hWY', hg⟩
    · exact b.rel_master hY
    · exact (not_inj₁_subset_inj₀ (h₁ Y hY) (hWX' ▸ hinj)).elim
    · exact b.mono hg (inj₁_subset_inj₁.mp (hWY' ▸ hinj)) subset_rfl hY hZ
  · intro hg
    exact ⟨inj₁ Y, ⟨b.rel_dom hg, Or.inr (Or.inr ⟨Y, b.rel_dom hg, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, b.rel_dom hg, rfl⟩), b.rel_cod hg,
      Or.inr (Or.inr ⟨Y, rfl, hg⟩)⟩

end DomainTheory.NeighbourhoodSystems
