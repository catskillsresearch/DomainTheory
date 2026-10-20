/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}










variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)










































































































/-- **Membership in `Xenum` for a single map.** A map `f` lies in `Xenum c` iff (when `c` is
consistent) it relates every coded step `⟨X₀ᵢ, X₁ⱼ⟩`; junk codes give `univ`. (The single-map analogue
of `mem_Xenum_iff`.) -/
theorem mem_Xenum_iff_map (gN : ℕ → ℕ) (f : ApproximableMap V₀ V₁) (c : ℕ) :
    f ∈ Xenum P₀ P₁ gN c ↔
      (gN c = 1 → ∀ e ∈ decodeList c, f.rel (P₀.X e.unpair.1) (P₁.X e.unpair.2)) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h, mem_stepFun]
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
    · intro _; exact Set.mem_univ f

end DomainTheory.NeighbourhoodSystems
