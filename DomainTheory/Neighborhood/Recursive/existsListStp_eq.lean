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









































































































































theorem existsListStp_eq (g : ℕ → ℕ) (acc x p : ℕ) :
    existsListStp g (Nat.pair x (Nat.pair acc p)) = selectFn acc 1 (isOne (g (Nat.pair x p))) := by
  unfold existsListStp; simp only [unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
