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


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

























/-- **Scott 1972, Corollary 3.4 (joint continuity, core).** Evaluation `[D → D'] × D → D'`,
`(f, x) ↦ f x`, preserves directed suprema. By Proposition 2.6 it suffices to check separate
Scott-continuity: in `x` (with `f` fixed) it is `f`'s own continuity, and in `f` (with `x` fixed)
it is the pointwise formula for suprema in `[D → D']` (`ScottMap.sSup_apply`). -/
theorem corollary_3_4_preservesDirectedSup :
    PreservesDirectedSup (fun p : ScottMap D D' × D => (p.1 : D → D') p.2) := by
  rw [proposition_2_6]
  constructor
  · intro y S hS hSdir
    show ((sSup S : ScottMap D D') : D → D') y
        = sSup ((fun x : ScottMap D D' => (x : D → D') y) '' S)
    rw [ScottMap.sSup_apply]
  · intro x
    exact (proposition_2_5 _).mp x.continuous

end DomainTheory.ContinuousLattice
