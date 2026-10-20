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


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]





/-- The infimum of a Scott-open neighbourhood of `y` is way below `y`: the open set is itself
the required witness. Scott uses this in moving between Definition 2.3 and Proposition 2.4. -/
theorem sInf_wayBelow {U : Set D} (hU : ScottOpen U) {y : D} (hy : y ∈ U) :
    sInf U ≪ y :=
  ⟨U, hU, hy, fun _ hz => Set.mem_Ici.2 (sInf_le hz)⟩

end DomainTheory.ContinuousLattice
