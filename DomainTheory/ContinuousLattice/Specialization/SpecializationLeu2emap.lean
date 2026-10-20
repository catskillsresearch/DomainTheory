/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.ContinuousLattice.WayBelow
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Order.ScottTopology
import Mathlib.Order.DirSupClosed
import DomainTheory.ContinuousLattice.Specialization.Basic


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]




/-- Continuous maps preserve Scott's specialization order. -/
theorem SpecializationLe.map {Y : Type*} [TopologicalSpace Y] {x y : X}
    (hxy : SpecializationLe x y) {f : X → Y} (hf : Continuous f) :
    SpecializationLe (f x) (f y) := by
  intro U hU hxU
  exact hxy (f ⁻¹' U) (hU.preimage hf) hxU

end DomainTheory.ContinuousLattice
