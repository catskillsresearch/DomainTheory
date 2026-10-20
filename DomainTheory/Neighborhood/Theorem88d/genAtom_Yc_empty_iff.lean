/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Theorem88b
import DomainTheory.Neighborhood.RecursiveCross
import DomainTheory.Neighborhood.Theorem88d.Basic
import DomainTheory.Neighborhood.Theorem88d.atomUCode_eq_genAtomYseqCode
import DomainTheory.Neighborhood.Theorem88d.atomUCode_inter_succ_empty_of_junk


namespace DomainTheory.Neighborhood

open NeighborhoodSystem Domain.Recursive

variable {α : Type*} {D : NeighborhoodSystem α} (P : ComputablePresentation D)






variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)


























































/-- **`Yc P`'s `genAtom`-emptiness matches `atomUEmpty` exactly** (the code-native analogue of
`atomU_invariant`'s emptiness-matching clause "(■)"): combines `atomUCode_eq_genAtomYseqCode`
(non-junk, giving a nonempty `UX`-image) with `atomUCode_inter_succ_empty_of_junk` (the genuine
transition to junk) by induction on `n`. -/
theorem genAtom_Yc_empty_iff (n k : ℕ) :
    genAtom (Yc P) U.master (deltaOf k) n = ∅ ↔ atomUEmpty P n k = 1 := by
  induction n with
  | zero =>
    have h0 : atomUEmpty P 0 k = 0 := by
      have hne : genAtom (idxSet (e P)) Set.univ (deltaOf k) 0 ≠ ∅ := by
        show (Set.univ : Set ℕ) ≠ ∅
        exact Set.univ_nonempty.ne_empty
      exact (atomUEmpty_eq_zero_iff_genAtom P 0 k).mpr hne
    constructor
    · intro h
      exact absurd h (Set.Nonempty.ne_empty U.master_mem.2.1)
    · intro h; omega
  | succ n ih =>
    have hle : atomUEmpty P (n + 1) k ≤ 1 := datomDec_le_one P _
    rcases (by omega : atomUEmpty P (n + 1) k = 0 ∨ atomUEmpty P (n + 1) k = 1) with h1 | h1
    · have heq' := atomUCode_eq_genAtomYseqCode P k (n + 1) h1
      constructor
      · intro hempty
        rw [← heq'] at hempty
        exact absurd hempty (U_mem_UX _).2.1.ne_empty
      · intro hcontra; omega
    · by_cases hn0 : atomUEmpty P n k = 0
      · have heq := atomUCode_eq_genAtomYseqCode P k n hn0
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [← heq]
          exact atomUCode_inter_succ_empty_of_junk P hn0 h1
        exact ⟨fun _ => h1, fun _ => hempty⟩
      · push Not at hn0
        have hle0 : atomUEmpty P n k ≤ 1 := datomDec_le_one P _
        have hn1 : atomUEmpty P n k = 1 := by omega
        have hprev : genAtom (Yc P) U.master (deltaOf k) n = ∅ := ih.mpr hn1
        have hempty : genAtom (Yc P) U.master (deltaOf k) (n + 1) = ∅ := by
          show genAtom (Yc P) U.master (deltaOf k) n ∩
            (if deltaOf k n then Yc P n else U.master \ Yc P n) = ∅
          rw [hprev, Set.empty_inter]
        exact ⟨fun _ => h1, fun _ => hempty⟩

end DomainTheory.Neighborhood
