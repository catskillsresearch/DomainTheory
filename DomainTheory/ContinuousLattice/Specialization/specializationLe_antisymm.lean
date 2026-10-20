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




theorem specializationLe_antisymm [T0Space X] {x y : X}
    (hxy : SpecializationLe x y) (hyx : SpecializationLe y x) : x = y :=
  Inseparable.eq (inseparable_iff_specializes_and.2
    ⟨specializes_iff_forall_open.2 fun s hs hy => hyx s hs hy,
     specializes_iff_forall_open.2 fun s hs hx => hxy s hs hx⟩)

end DomainTheory.ContinuousLattice
