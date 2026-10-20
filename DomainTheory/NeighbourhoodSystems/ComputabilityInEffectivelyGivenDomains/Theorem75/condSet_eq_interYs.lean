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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.mem_condSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- `condSet k Δ₁ el` is exactly `interYs Δ₁ (funListOf el) (X₀_k)`. -/
theorem condSet_eq_interYs (k : ℕ) (el : List ℕ) :
    condSet P₀ P₁ k V₁.master el = interYs V₁.master (funListOf P₀ P₁ el) (P₀.X k) := by
  ext z
  rw [mem_interYs, mem_condSet]
  constructor
  · rintro ⟨hz, hall⟩
    refine ⟨hz, ?_⟩
    intro p hp hsub
    rw [funListOf, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact hall e he hsub
  · rintro ⟨hz, hall⟩
    exact ⟨hz, fun e he hsub => hall (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩) hsub⟩

end DomainTheory.NeighbourhoodSystems
