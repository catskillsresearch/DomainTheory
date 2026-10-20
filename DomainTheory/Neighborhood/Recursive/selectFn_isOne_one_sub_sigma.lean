/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic
import Mathlib.Computability.Partrec
import Mathlib.Tactic.Ring
import DomainTheory.Neighborhood.Exercise722Regular
import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv
import DomainTheory.Neighborhood.Recursive.Basic


namespace Domain.Recursive





















































































































































































theorem selectFn_isOne_one_sub_sigma (u : ℕ) :
    selectFn (isOne (1 - u)) 1 0 = 1 ↔ u = 0 := by
  constructor
  · intro h
    by_cases hu : u = 0
    · exact hu
    · have : isOne (1 - u) = 0 := isOne_of_ne_one (by omega)
      simp [this, selectFn_zero] at h
  · intro hu
    subst hu
    simp [isOne_one, selectFn_one]

end Domain.Recursive
