/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Recursive
public import DomainTheory.Neighborhood.RationalPrimrec.Basic
public import DomainTheory.Neighborhood.RationalPrimrec.ratLeCode_eq_one_iff
public import DomainTheory.Neighborhood.RationalPrimrec.ratLeCode_le_one

@[expose] public section


namespace DomainTheory.Neighborhood

open Domain.Recursive



















theorem decodeRat_ratMinCode (c1 c2 : ℕ) :
    decodeRat (ratMinCode (Nat.pair c1 c2)) = min (decodeRat c1) (decodeRat c2) := by
  unfold ratMinCode
  rw [unpair_pair_fst, unpair_pair_snd]
  by_cases h : decodeRat c1 ≤ decodeRat c2
  · rw [(ratLeCode_eq_one_iff c1 c2).mpr h, selectFn_one, min_eq_left h]
  · have hf : ratLeCode (Nat.pair c1 c2) ≠ 1 := fun he => h ((ratLeCode_eq_one_iff c1 c2).mp he)
    have hf0 : ratLeCode (Nat.pair c1 c2) = 0 := by
      have := ratLeCode_le_one (Nat.pair c1 c2); omega
    rw [hf0, selectFn_zero, min_eq_right ((not_le.mp h).le)]

end DomainTheory.Neighborhood
