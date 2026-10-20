/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
import DomainTheory.DataTypesAsLattices.Closures.boxShift_app_ne_bot
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 / analogue of 4.5.** Right injection into the
paper sum, on the shifted summand. -/
theorem boxPlus_typed_inr {a b y : Pomega} (hy : typed y (boxShift b)) :
    typed (squarePair botElem y) (boxPlus a b) := by
  have hy0 : y ≠ botElem := by
    rw [hy]; exact boxShift_app_ne_bot b y
  rw [typed, boxPlus_app_right (eq_5_9 _ _) (by rw [eq_5_10]; exact hy0), eq_5_10,
    ← hy]

end DomainTheory.DataTypesAsLattices
