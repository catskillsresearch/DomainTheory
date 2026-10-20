/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.mem_upSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- `X ↦ ↑X` is inclusion-**preserving**: `↑X ⊆ ↑Y ↔ X ⊆ Y` (for `X ∈ 𝒟`).
`→` tests at `X ∈ ↑X`; `←` is transitivity of `⊆`. -/
theorem upSet_subset_iff {X Y : Set α} (hX : V.mem X) : V.upSet X ⊆ V.upSet Y ↔ X ⊆ Y := by
  constructor
  · intro h
    exact (h ⟨hX, subset_rfl⟩).2
  · intro hXY Z hZ
    exact ⟨hZ.1, hZ.2.trans hXY⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
