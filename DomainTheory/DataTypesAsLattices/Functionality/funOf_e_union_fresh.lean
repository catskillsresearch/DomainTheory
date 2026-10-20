/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices



























theorem funOf_e_union_fresh (p j m : ℕ) (u : Pomega) (hpj : p < j) :
    funOf (e p) (u ∪ {pair j m}) = funOf (e p) u := by
  apply subset_antisymm
  · intro k hk
    obtain ⟨r, hr, hprk⟩ := hk
    refine ⟨r, ?_, hprk⟩
    intro t ht
    rcases hr ht with htu | htag
    · exact htu
    · have htEq : t = pair j m := by simpa using htag
      have hjr : j ≤ r := by
        rw [htEq] at ht
        exact (pair_le_left j m).trans (mem_e_le ht)
      have hrp : r ≤ p := (pair_le_left r k).trans (mem_e_le hprk)
      exact (Nat.not_lt_of_ge (hjr.trans hrp) hpj).elim
  · exact funOf_monotone_right (e p) Set.subset_union_left

end DomainTheory.DataTypesAsLattices
