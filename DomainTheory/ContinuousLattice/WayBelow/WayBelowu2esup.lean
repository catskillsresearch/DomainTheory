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
import DomainTheory.ContinuousLattice.WayBelow.scottOpen_inter


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]




/-- **Scott 1972, Proposition 2.2(ii).** `x ≪ z` and `y ≪ z` imply `x ⊔ y ≪ z`. -/
theorem WayBelow.sup {x y z : D} (hx : x ≪ z) (hy : y ≪ z) : x ⊔ y ≪ z := by
  obtain ⟨U, hU, hzU, hUsub⟩ := hx
  obtain ⟨V, hV, hzV, hVsub⟩ := hy
  refine ⟨U ∩ V, scottOpen_inter hU hV, ⟨hzU, hzV⟩, fun w hw => ?_⟩
  exact Set.mem_Ici.2 (sup_le (hUsub hw.1) (hVsub hw.2))

end DomainTheory.ContinuousLattice
