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
import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapPointwiseTopology_eq_induced_pi
import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_topology


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
























/-- The literal product/subspace form of Theorem 3.3: the Scott lattice topology on `[D → D']`
is induced from Mathlib's Pi topology on the underlying functions. -/
theorem theorem_3_3_topology_induced_pi (hD : IsContinuousLattice D)
    (hD' : IsContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
      scottMapInducedPiTopology D D' := by
  rw [theorem_3_3_topology hD hD', scottMapPointwiseTopology_eq_induced_pi]

end DomainTheory.ContinuousLattice
