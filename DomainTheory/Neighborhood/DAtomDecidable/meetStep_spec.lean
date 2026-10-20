/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88a
import DomainTheory.Neighborhood.Definition71
import DomainTheory.Neighborhood.DAtomDecidable.Basic
import DomainTheory.Neighborhood.DAtomDecidable.meetStep_ok_le_one


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable (cons : ℕ → ℕ)




/-- **One-step transfer of the meet-fold invariant**: if `init` codes `(ok, idx)` faithfully
relative to some set `S` (`ok = 1 → idxSet idx = S`, `ok = 0 → S = ∅`), then `meetStep init i`
codes the same relative to `S ∩ idxSet i` — the positive constraint contributed by `i`. -/
theorem meetStep_spec
    (hcons : ∀ n m, cons (Nat.pair n m) = 1 ↔ ∃ k, P.X k ⊆ P.X n ∩ P.X m)
    {init : ℕ} {S : Set ℕ} (hle : init.unpair.1 ≤ 1)
    (h1 : init.unpair.1 = 1 → idxSet P.X init.unpair.2 = S)
    (h0 : init.unpair.1 = 0 → S = ∅) (i : ℕ) :
    (meetStep P cons init i).unpair.1 ≤ 1 ∧
      ((meetStep P cons init i).unpair.1 = 1 →
        idxSet P.X (meetStep P cons init i).unpair.2 = S ∩ idxSet P.X i) ∧
      ((meetStep P cons init i).unpair.1 = 0 → S ∩ idxSet P.X i = ∅) := by
  refine ⟨meetStep_ok_le_one P cons init i, ?_, ?_⟩ <;>
    (unfold meetStep
     rcases (show init.unpair.1 = 0 ∨ init.unpair.1 = 1 by omega) with hi | hi)
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro h; exact absurd h (by decide)
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro h; exact absurd h (by decide)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_snd, unpair_pair_fst]
      intro _
      have heq : P.X init.unpair.2 ∩ P.X i = P.X (P.inter init.unpair.2 i) :=
        (P.inter_spec (hcons _ _ |>.mp hc)).symm
      rw [← idxSet_inter_of_inter_eq (e := P.X) heq, h1 hi]
  · rw [hi, isOne_zero, Nat.zero_mul, selectFn_zero, unpair_pair_fst]
    intro _
    rw [h0 hi]; simp
  · rw [hi, isOne_one, Nat.one_mul]
    have hc_dec : ((cons (Nat.pair init.unpair.2 i)) ≠ 1) ∨ ((cons (Nat.pair init.unpair.2 i)) = 1) := by
      by_cases hc : (cons (Nat.pair init.unpair.2 i)) = 1
      · exact Or.inr hc
      · exact Or.inl hc
    rcases hc_dec with hc | hc
    · rw [isOne_of_ne_one hc, selectFn_zero, unpair_pair_fst]
      intro _
      rw [← h1 hi]
      ext m
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hm1 hm2
      exact hc ((hcons _ _).mpr ⟨m, Set.subset_inter hm1 hm2⟩)
    · rw [(isOne_eq_one_iff _).mpr hc, selectFn_one, unpair_pair_fst]
      intro h; exact absurd h (by decide)

end DomainTheory.Neighborhood
