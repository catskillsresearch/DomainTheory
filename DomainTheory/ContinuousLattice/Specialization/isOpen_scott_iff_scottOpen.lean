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
import DomainTheory.ContinuousLattice.Specialization.isOpen_iff_scottOpen


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]






/-- Scott-open sets in our sense agree with mathlib's Scott topology (alias). -/
theorem isOpen_scott_iff_scottOpen {U : Set D} :
    @IsOpen D (Topology.scott D univ) U ↔ ScottOpen U :=
  isOpen_iff_scottOpen

end DomainTheory.ContinuousLattice
