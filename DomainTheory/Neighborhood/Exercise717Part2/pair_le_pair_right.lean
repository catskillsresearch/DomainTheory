/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise717
import DomainTheory.Neighborhood.Exercise510
import DomainTheory.Neighborhood.Proposition77
import DomainTheory.Neighborhood.Exercise717Part2.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717



variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}
















/-- `Nat.pair` is monotone in its second argument (first argument fixed). -/
theorem pair_le_pair_right {a b d : ℕ} (h : b ≤ d) : Nat.pair a b ≤ Nat.pair a d := by
  unfold Nat.pair
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [ite_eq_left hab, ite_eq_left (lt_of_lt_of_le hab h)]
    have : b * b ≤ d * d := Nat.mul_le_mul h h
    omega
  · rw [ite_eq_right (Nat.not_lt.mpr hab)]
    rcases Nat.lt_or_ge a d with had | had
    · rw [ite_eq_left had]
      have h1 : a * a + a ≤ d * d := by
        calc a * a + a = a * (a + 1) := by ring
          _ ≤ a * d := Nat.mul_le_mul (le_refl a) had
          _ ≤ d * d := Nat.mul_le_mul had.le (le_refl d)
      omega
    · rw [ite_eq_right (Nat.not_lt.mpr had)]; omega

end Exercise717
end DomainTheory.Neighborhood
