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















































































/-- The decoded list is no longer than its code. -/
theorem decodeList_length_le (c : ℕ) : (decodeList c).length ≤ c := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    cases c with
    | zero => simp [decodeList_zero]
    | succ d =>
      rw [decodeList_succ, List.length_cons]
      have hle := unpair_snd_le d
      have := ih d.unpair.2 (Nat.lt_succ_of_le hle)
      omega

end Domain.Recursive
