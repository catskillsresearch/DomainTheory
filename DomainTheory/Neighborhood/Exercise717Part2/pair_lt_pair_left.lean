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
















/-- `Nat.pair` is strictly monotone in its first argument (second argument fixed). -/
theorem pair_lt_pair_left {a c b : ℕ} (h : a < c) : Nat.pair a b < Nat.pair c b := by
  unfold Nat.pair
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [ite_eq_left hab]
    rcases Nat.lt_or_ge c b with hcb | hcb
    · rw [ite_eq_left hcb]; omega
    · rw [ite_eq_right (Nat.not_lt.mpr hcb)]
      have hbc : b * b ≤ c * c := Nat.mul_le_mul hcb hcb
      omega
  · rw [ite_eq_right (Nat.not_lt.mpr hab),
      ite_eq_right (Nat.not_lt.mpr (le_of_lt (lt_of_le_of_lt hab h)))]
    have hcc : (a + 1) * (a + 1) ≤ c * c := Nat.mul_le_mul h h
    have hexp : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
    omega

end Exercise717
end DomainTheory.Neighborhood
