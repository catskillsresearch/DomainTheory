/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_apply_of_wayBelow
import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_wayBelow
import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_pointwise_sSup


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']




















/-- **Scott 1972, Theorem 3.3 (order content).** If `D` and `D'` are continuous lattices, then so
is `[D → D']` under the pointwise order. Every `f` is the supremum of the step functions way below
it: `f = ⊔ {ē[e,e'] | e' ≪ f e}`, and each such step function is way below `f`. -/
theorem theorem_3_3_isContinuousLattice (hD : IsContinuousLattice D)
    (hD' : IsContinuousLattice D') : IsContinuousLattice (ScottMap D D') := by
  intro f
  refine ⟨fun h hh => hh.le, fun g hg => ?_⟩
  rw [ScottMap.le_def]
  intro x
  rw [← stepMap_pointwise_sSup hD hD' f x]
  refine sSup_le ?_
  rintro e' ⟨e, hex, he'⟩
  have hle : stepMap e e' ≤ g := hg (stepMap_wayBelow he')
  have hx := (ScottMap.le_def.1 hle) x
  rwa [stepMap_apply_of_wayBelow hex] at hx

end DomainTheory.ContinuousLattice
