/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Words.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722


theorem mem_wordsUpTo (n : ℕ) {w : List Bool} : w ∈ wordsUpTo n ↔ w.length ≤ n := by
  induction n generalizing w with
  | zero =>
    simp only [wordsUpTo, List.mem_singleton]
    constructor
    · rintro (rfl : w = [])
      simp
    · intro h
      exact (List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero h)).symm ▸ rfl
  | succ n ih =>
    simp only [wordsUpTo]
    rw [List.mem_append, List.mem_flatMap]
    constructor
    · intro h
      rcases h with h | ⟨w', hw', hmem⟩
      · exact Nat.le_succ_of_le (ih.mp h)
      · rw [List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · simpa [List.length_cons] using Nat.succ_le_succ (ih.mp hw')
        · simpa [List.length_cons] using Nat.succ_le_succ (ih.mp hw')
    · intro hlen
      by_cases hw : w.length ≤ n
      · exact Or.inl (ih.mpr hw)
      · match w with
        | [] => exfalso; exact hw (by simp)
        | hd :: tl =>
          have htl_len : tl.length ≤ n := by
            have : tl.length + 1 ≤ n + 1 := by simpa [List.length_cons] using hlen
            exact Nat.le_of_succ_le_succ this
          have htl : tl ∈ wordsUpTo n := ih.mpr htl_len
          refine Or.inr ⟨tl, htl, ?_⟩
          rw [List.mem_cons, List.mem_singleton]
          cases hd with
          | false => exact Or.inl rfl
          | true => exact Or.inr rfl

end Exercise722
end DomainTheory.NeighbourhoodSystems
