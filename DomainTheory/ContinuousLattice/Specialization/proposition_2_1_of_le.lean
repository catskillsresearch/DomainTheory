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

/-- **Scott 1972, Proposition 2.1 (backward).** If `y ≤ L` and `L` is  the lub of a monotone
net, then the net converges to `y` in the Scott topology. -/
theorem proposition_2_1_of_le [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L)
    (hyL : y ≤ L) : ScottConvergesTo x y := by
  intro U hU hyU
  have hdir : DirectedOn (· ≤ ·) (range x) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    exact ⟨x k, ⟨k, rfl⟩, hx hik, hx hjk⟩
  have hLU : sSup (range x) ∈ U := by
    rw [IsLUB.sSup_eq hL]
    exact hU.1 hyL hyU
  obtain ⟨s, hsS, hsU⟩ := hU.2 (Set.range_nonempty x) hdir hLU
  obtain ⟨i₀, rfl⟩ := hsS
  refine ⟨i₀, fun j hj => hU.1 (hx hj) hsU⟩

end DomainTheory.ContinuousLattice
