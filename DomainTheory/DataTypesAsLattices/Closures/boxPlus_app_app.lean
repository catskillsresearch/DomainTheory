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
import DomainTheory.DataTypesAsLattices.Closures.boxShift_isRetract
import DomainTheory.DataTypesAsLattices.Closures.boxShift_app_ne_bot
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_left
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_right
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_mixed
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_empty
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_bot
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_top


namespace DomainTheory.DataTypesAsLattices































theorem boxPlus_app_app {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b)
    (u : Pomega) :
    funOf (boxPlus a b) (funOf (boxPlus a b) u) = funOf (boxPlus a b) u := by
  by_cases hx : squareFst u = botElem <;> by_cases hy : squareSnd u = botElem
  · rw [boxPlus_app_empty hx hy, boxPlus_app_bot]
  · rw [boxPlus_app_right hx hy,
      boxPlus_app_right (u := squarePair botElem (funOf (boxShift b) (squareSnd u)))
        (eq_5_9 _ _) (by rw [eq_5_10]; exact boxShift_app_ne_bot b _),
      eq_5_10, retract_app (boxShift_isRetract hb)]
  · rw [boxPlus_app_left hx hy,
      boxPlus_app_left (u := squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (by rw [eq_5_9]; exact boxShift_app_ne_bot a _) (eq_5_10 _ _),
      eq_5_9, retract_app (boxShift_isRetract ha)]
  · rw [boxPlus_app_mixed hx hy, boxPlus_app_top]

end DomainTheory.DataTypesAsLattices
