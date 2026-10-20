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
import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_isContinuousLattice
import DomainTheory.ContinuousLattice.FunctionSpaces.theorem_3_3_topology


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
























/-- **Scott 1972, Theorem 3.3 (full statement).** For continuous lattices `D`, `D'`, the function
space `[D → D']` is a continuous lattice (`theorem_3_3_isContinuousLattice`) whose Scott topology
agrees with the topology of pointwise convergence (`theorem_3_3_topology`). -/
theorem theorem_3_3 (hD : IsContinuousLattice D) (hD' : IsContinuousLattice D') :
    IsContinuousLattice (ScottMap D D') ∧
      (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) = scottMapPointwiseTopology D D' :=
  ⟨theorem_3_3_isContinuousLattice hD hD', theorem_3_3_topology hD hD'⟩

end DomainTheory.ContinuousLattice
