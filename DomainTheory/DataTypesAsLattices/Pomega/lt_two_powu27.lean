/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Lattice.Bounded
import Mathlib.Data.Set.Lattice.Disjoint
import DomainTheory.DataTypesAsLattices.Pomega.Basic


namespace DomainTheory.DataTypesAsLattices









theorem lt_two_pow' (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    calc
      k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt ih
      _ < 2 ^ k + 2 ^ k := Nat.lt_add_of_pos_right (Nat.two_pow_pos k)
      _ = 2 ^ (k + 1) := by rw [← Nat.two_mul, Nat.mul_comm, Nat.pow_succ]

end DomainTheory.DataTypesAsLattices
