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
import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10_a
import DomainTheory.ContinuousLattice.FunctionSpaces.proposition_2_10_b


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']







































/-- **Scott 1972, Proposition 2.10 (full statement).** A retract of a continuous lattice is a
continuous lattice (`proposition_2_10_a`) whose Scott topology agrees with the subspace topology
(`proposition_2_10_b`). -/
theorem proposition_2_10 (R : IsContinuousLatticeRetraction D D')
    (hD' : IsContinuousLattice D') :
    IsContinuousLattice D ∧
      (scottTopologicalSpace : TopologicalSpace D) =
        TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace :=
  ⟨proposition_2_10_a R hD', proposition_2_10_b R hD'⟩

end DomainTheory.ContinuousLattice
