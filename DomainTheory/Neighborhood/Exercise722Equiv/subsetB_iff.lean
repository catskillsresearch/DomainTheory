/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise722Decide
import DomainTheory.Neighborhood.Exercise722Equiv.Basic
import DomainTheory.Neighborhood.Exercise722Equiv.exists_diff_word_short


namespace DomainTheory.Neighborhood

namespace Exercise722

open scoped Computability
open Sum Set












theorem subsetB_iff (e1 e2 : SExpr) : subsetB e1 e2 = true ↔ denote e1 ⊆ denote e2 := by
  unfold subsetB
  rw [List.all_eq_true]
  constructor
  · intro h
    by_contra hsub
    obtain ⟨w, hlen, hw1, hw2⟩ := exists_diff_word_short hsub
    have hwmem : w ∈ wordsUpTo (Fintype.card (Finset (autState e1) × Finset (autState e2))) :=
      (mem_wordsUpTo _).mpr (le_of_lt hlen)
    have hor := h w hwmem
    have he1 : matchesB e1 w = true := (matchesB_iff e1 w).mpr hw1
    rw [he1] at hor
    simp only [Bool.not_true, Bool.false_or] at hor
    exact hw2 ((matchesB_iff e2 w).mp hor)
  · intro hsub w _
    by_cases hw1 : w ∈ denote e1
    · have he2 : matchesB e2 w = true := (matchesB_iff e2 w).mpr (hsub hw1)
      simp [he2]
    · have he1 : matchesB e1 w = false := by
        rw [Bool.eq_false_iff]
        intro hc
        exact hw1 ((matchesB_iff e1 w).mp hc)
      simp [he1]

end Exercise722
end DomainTheory.Neighborhood
