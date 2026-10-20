/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.FunctionSpace
import DomainTheory.Neighborhood.Definition72
import DomainTheory.Neighborhood.Theorem74
import DomainTheory.Neighborhood.Theorem75.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)








































































































/-- **Bridge.** `φ ∋ Xenum c` iff, *when `c` is consistent*, `φ` contains every constituent step. -/
theorem mem_Xenum_iff (gN : ℕ → ℕ) (φ : (funSpace V₀ V₁).Element) (c : ℕ) :
    φ.mem (Xenum P₀ P₁ gN c) ↔
      (gN c = 1 → ∀ e ∈ decodeList c, φ.mem (step (P₀.X e.unpair.1) (P₁.X e.unpair.2))) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h, mem_stepFun_iff φ (funListOf_valid P₀ P₁ (decodeList c))]
    constructor
    · intro hp _ e he
      exact hp (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    · intro himp p hp
      rw [funListOf, List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact himp h e he
  · rw [Xenum_neg P₀ P₁ h]
    constructor
    · intro _ hcon; exact absurd hcon h
    · intro _; rw [← funSpace_master]; exact φ.master_mem

end DomainTheory.Neighborhood
