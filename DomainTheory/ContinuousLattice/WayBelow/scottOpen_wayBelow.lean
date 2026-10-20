/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Directed
import DomainTheory.ContinuousLattice.WayBelow.Basic
import DomainTheory.ContinuousLattice.WayBelow.WayBelowu2etrans_le


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]




/-- Auxiliary: the up-set `{z | x ≪ z}` is itself Scott-open. (This is *not* Scott's
Proposition 2.2(vi) — see `wayBelow_self_iff_scottOpen_Ici` for that — but it is a standard
and useful fact, the openness of the sets `↟x`.) -/
theorem scottOpen_wayBelow (x : D) : ScottOpen {z | x ≪ z} := by
  refine ⟨fun a b hab ha => ha.trans_le hab, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hU, hsupU, hsub⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
  exact ⟨s, hsS, ⟨U, hU, hsU, hsub⟩⟩

end DomainTheory.ContinuousLattice
