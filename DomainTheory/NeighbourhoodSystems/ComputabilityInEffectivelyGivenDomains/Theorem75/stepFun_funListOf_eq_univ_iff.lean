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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.botMap
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.botMap_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- **`stepFun (funListOf el)` is everything iff every output neighbourhood is `Δ₁`.** Forward:
the bottom map `botMap` lies in `univ`, and `botMap.rel X Y` forces `Y = Δ₁`. Backward: `[X, Δ₁]`
is satisfied by every map. Choice-free. -/
theorem stepFun_funListOf_eq_univ_iff (el : List ℕ) :
    (stepFun (funListOf P₀ P₁ el) : Set (ApproximableMap V₀ V₁)) = Set.univ ↔
      ∀ e ∈ el, P₁.X e.unpair.2 = V₁.master := by
  constructor
  · intro h e he
    have hbot : (botMap : ApproximableMap V₀ V₁) ∈ stepFun (funListOf P₀ P₁ el) := by
      rw [h]; exact Set.mem_univ _
    have hr := hbot (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    exact Set.Subset.antisymm (V₁.sub_master (P₁.mem_X _)) (botMap_rel.mp hr).2.2
  · intro h
    ext f
    simp only [Set.mem_univ, iff_true, mem_stepFun]
    intro p hp
    rw [funListOf, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    show f.rel (P₀.X e.unpair.1) (P₁.X e.unpair.2)
    rw [h e he]
    exact f.mono f.master_rel (V₀.sub_master (P₀.mem_X _)) subset_rfl (P₀.mem_X _) V₁.master_mem

end DomainTheory.NeighbourhoodSystems
