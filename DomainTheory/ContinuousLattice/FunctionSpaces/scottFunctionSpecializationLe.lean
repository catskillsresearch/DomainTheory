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
import DomainTheory.ContinuousLattice.FunctionSpaces.scottFunctionSubbasis_isOpen
import DomainTheory.ContinuousLattice.FunctionSpaces.specializationLe_generateOpen


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']







theorem scottFunctionSpecializationLe {f g : C(X, Y)} :
    letI := scottFunctionTopology X Y
    SpecializationLe f g ↔ ∀ x, SpecializationLe (f x) (g x) := by
  let : TopologicalSpace (C(X, Y)) := scottFunctionTopology X Y
  constructor
  · intro hfg x U hU hfU
    exact hfg {h | h x ∈ U} (scottFunctionSubbasis_isOpen (X := X) (Y := Y) hU) hfU
  · intro hfg U hU hfU
    exact specializationLe_generateOpen f g hfg hU hfU

end DomainTheory.ContinuousLattice
