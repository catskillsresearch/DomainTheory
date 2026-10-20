/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Basic.Real.Basic
import all Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
import all Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import all Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalMem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.inter_mem'
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise117.ratIntervalSystem_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace RatInterval

open NeighborhoodSystem

/-- **Exercise 1.17 — the point filter `{X ∈ 𝒟 ∣ t ∈ X}`.** For any real `t` this is a filter:
closure under `∩` uses `inter_mem'` with `t` itself as the shared point. -/
def filterAt (t : ℝ) : ratIntervalSystem.Element where
  mem X := ratIntervalMem X ∧ t ∈ X
  sub h := h.1
  master_mem := ⟨Or.inl rfl, Set.mem_univ t⟩
  inter_mem := by
    rintro X Y ⟨hX, htX⟩ ⟨hY, htY⟩
    exact ⟨inter_mem' hX hY ⟨t, htX, htY⟩, htX, htY⟩
  up_mem := by
    rintro X Y ⟨_, htX⟩ hY hXY
    exact ⟨hY, hXY htX⟩

end RatInterval

end DomainTheory.NeighbourhoodSystems
