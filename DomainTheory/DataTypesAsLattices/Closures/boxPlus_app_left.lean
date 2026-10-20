/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.union_botElem
import DomainTheory.DataTypesAsLattices.Closures.exists_mem_of_ne_bot
import DomainTheory.DataTypesAsLattices.Closures.boxTag_bot
import DomainTheory.DataTypesAsLattices.Closures.boxTag_of_mem
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app


namespace DomainTheory.DataTypesAsLattices































/-- Occupancy test of (5.13): only the left component is inhabited. -/
theorem boxPlus_app_left {a b u : Pomega} (hx : squareFst u ≠ botElem)
    (hy : squareSnd u = botElem) :
    funOf (boxPlus a b) u =
      squarePair (funOf (boxShift a) (squareFst u)) botElem := by
  obtain ⟨m, hm⟩ := exists_mem_of_ne_bot hx
  rw [boxPlus_app, boxTag_of_mem hm, hy, boxTag_bot, union_botElem,
    dcondSet_ofNat_zero]

end DomainTheory.DataTypesAsLattices
