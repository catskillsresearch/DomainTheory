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
import DomainTheory.ContinuousLattice.Specialization.ScottOpen_iff_dirSupInacc


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]






theorem isOpen_iff_scottOpen {U : Set D} : @IsOpen D scottTopologicalSpace U ↔ ScottOpen U := by
  rw [ScottOpen_iff_dirSupInacc, scottTopologicalSpace]
  have hinst : @IsScott D univ _ (Topology.scott D univ) :=
    @IsScott.mk D univ _ (Topology.scott D univ) rfl
  simpa [dirSupInaccOn_univ] using
    @IsScott.isOpen_iff_isUpperSet_and_dirSupInaccOn D univ _ (Topology.scott D univ) U hinst

end DomainTheory.ContinuousLattice
