/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.exists_mem_of_ne_bot
import DomainTheory.DataTypesAsLattices.Closures.boxTag_of_mem
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app


namespace DomainTheory.DataTypesAsLattices































/-- Occupancy test of (5.13): both components inhabited, so (4.4) gives `⊤`. -/
theorem boxPlus_app_mixed {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u ≠ botElem) :
    funOf (boxPlus a b) u = topElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  obtain ⟨k, hk⟩ := exists_mem_of_ne_bot hy
  rw [boxPlus_app, boxTag_of_mem hm, boxTag_of_mem hk]
  exact dcondSet_of_mixed (by simp [ofNat]) ⟨0, by simp [ofNat]⟩

end DomainTheory.DataTypesAsLattices
