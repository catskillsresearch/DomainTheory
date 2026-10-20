/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Exercise222
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.mem_graph
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.C
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.joinMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.sUnion_eq_graph_joinMap

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise327

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- **Exercise 2.22 hypothesis (ii).** `C` is closed under directed unions. -/
theorem C_dir : ∀ 𝒮 : Set (Set (Set α × Set β)), 𝒮.Nonempty → 𝒮 ⊆ C V₀ V₁ →
    DirectedOn (· ⊆ ·) 𝒮 → ⋃₀ 𝒮 ∈ C V₀ V₁ := by
  intro 𝒮 hne h𝒮 hdir
  rw [sUnion_eq_graph_joinMap 𝒮 h𝒮 hne hdir]
  exact ⟨joinMap 𝒮 h𝒮 hne hdir, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise327
