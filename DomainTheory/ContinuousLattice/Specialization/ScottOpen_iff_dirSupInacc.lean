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






theorem ScottOpen_iff_dirSupInacc {U : Set D} : ScottOpen U ↔ IsUpperSet U ∧ DirSupInacc U := by
  constructor
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ a ha hmem => ?_⟩
    rw [← IsLUB.sSup_eq ha] at hmem
    obtain ⟨s, hs, hsU⟩ := hU' hd₁ hd₂ hmem
    exact ⟨s, hs, hsU⟩
  · intro ⟨hU, hU'⟩
    refine ⟨hU, fun d hd₁ hd₂ hmem => ?_⟩
    obtain ⟨s, hs, hsU⟩ := hU' hd₁ hd₂ (isLUB_sSup d) hmem
    exact ⟨s, hs, hsU⟩

end DomainTheory.ContinuousLattice
