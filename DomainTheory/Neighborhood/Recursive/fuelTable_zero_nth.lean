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













































































































































































theorem fuelTable_zero_nth {bodyLookup : ℕ → ℕ} {bound i : ℕ} (hi : i ≤ bound) (d : ℕ) :
    nthCode (fuelTable bodyLookup bound 0) i d = 0 := by
  show nthCode (tabCode (fun _ => 0) (Nat.pair (bound + 1) 0) (bound + 1)) i d = 0
  rw [tabCode_nth_lt (show i < bound + 1 by omega)]

end Domain.Recursive
