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




/-- Scott's specialization order is the reverse of Mathlib's `Specializes` convention. -/
theorem specializationLe_iff_specializes {x y : X} :
    SpecializationLe x y ↔ y ⤳ x :=
  specializes_iff_forall_open.symm

end DomainTheory.ContinuousLattice
