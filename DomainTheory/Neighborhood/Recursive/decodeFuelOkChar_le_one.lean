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























































































































































































theorem decodeFuelOkChar_le_one : ∀ fuel c, decodeFuelOkChar fuel c ≤ 1
  | 0, _ => by simp [decodeFuelOkChar]
  | fuel + 1, c => by
    rw [decodeFuelOkChar, decodeFuelOkCharBody_eq]
    match tag : c.unpair.1 with
    | 0 =>
      simp
      rcases (show isOne (1 - c.unpair.2) = 0 ∨ isOne (1 - c.unpair.2) = 1 by
        have := isOne_le_one (1 - c.unpair.2); omega) with h0 | h1
      · rw [h0, selectFn_zero]; exact Nat.zero_le 1
      · rw [h1, selectFn_one]
    | 1 =>
      simp
      exact allBinDigitsChar_le_one _
    | 2 | 3 =>
      simp
      exact mulBit_le_one (decodeFuelOkChar_le_one fuel c.unpair.2.unpair.1)
        (decodeFuelOkChar_le_one fuel c.unpair.2.unpair.2)
    | _ + 4 =>
      simp

end Domain.Recursive
