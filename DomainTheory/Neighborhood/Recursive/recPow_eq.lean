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



















































































/-- `Nat.rec 1 (· * b)` computes `b ^ e` (choice-free). -/
theorem recPow_eq (b : ℕ) :
    ∀ e, Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => ih * b) e = b ^ e
  | 0 => (pow_zero b).symm
  | e + 1 => by rw [pow_succ]; exact congrArg (· * b) (recPow_eq b e)

end Domain.Recursive
