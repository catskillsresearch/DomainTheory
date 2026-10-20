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







variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]



variable {x : ι → D} {L y : D}

/-- The complement of a principal lower set `Iic L` is Scott-open: it is an upper set, and it
is inaccessible by directed suprema because if every member of a directed `S` lies below `L`
then so does `⊔S`. -/
theorem scottOpen_not_le (L : D) : ScottOpen {z : D | ¬ z ≤ L} := by
  refine ⟨fun a b hab ha hb => ha (le_trans hab hb), fun S hSne hSdir hmem => ?_⟩
  by_contra hcon
  refine hmem (sSup_le fun s hs => ?_)
  by_contra hsL
  exact hcon ⟨s, hs, hsL⟩

end DomainTheory.ContinuousLattice
