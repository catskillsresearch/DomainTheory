/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise817
public import DomainTheory.Neighborhood.Proposition810b
public import DomainTheory.Neighborhood.Exercise326Sum
public import DomainTheory.Neighborhood.Exercise315
public import DomainTheory.Neighborhood.Exercise819.Basic

@[expose] public section


namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap Exercise326

universe u




section SumHelpers

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- **`out₀ ∘ in₁ = const ⊥`.** A right-injected element carries no left-hand information. -/
theorem outMap₀_comp_inMap₁ :
    (outMap₀ (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁)).comp
        (inMap₁ (h₀ := h₀) (h₁ := h₁)) = constMap V₁ V₀.bot := by
  apply ApproximableMap.ext
  intro Y Z
  rw [constMap_rel, mem_bot]
  constructor
  · rintro ⟨W, ⟨hY, hWmem, hinj⟩, _, hZ, hsub⟩
    refine ⟨hY, ?_⟩
    obtain ⟨b, hb⟩ := h₁ Y hY
    have hmaster : leftPart V₀ (inj₁ Y) ⊆ leftPart V₀ W := leftPart_mono V₀ hinj
    rw [leftPart_inj₁ V₀ ⟨b, hb⟩] at hmaster
    exact Set.Subset.antisymm (V₀.sub_master hZ) (hmaster.trans hsub)
  · rintro ⟨hY, rfl⟩
    exact ⟨inj₁ Y, ⟨hY, Or.inr (Or.inr ⟨Y, hY, rfl⟩), subset_rfl⟩,
      Or.inr (Or.inr ⟨Y, hY, rfl⟩), V₀.master_mem, (leftPart_inj₁ V₀ (h₁ Y hY)).subset⟩

end SumHelpers
end DomainTheory.Neighborhood
