/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Graph
import DomainTheory.DataTypesAsLattices.FixedPoint.Basic
import DomainTheory.DataTypesAsLattices.FixedPoint.exists_index_of_finset


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Appendix lemma.** Continuous maps preserve ascending
countable unions. -/
theorem chain_lemma {f : Pomega → Pomega} (hf : IsScottContinuous f)
    (xs : ℕ → Pomega) (hmono : ∀ n, xs n ⊆ xs (n + 1)) :
    f (⋃ n, xs n) = ⋃ n, f (xs n) := by
  apply subset_antisymm
  · intro k hk
    have hchar := (theorem_1_1 f).mp hf (⋃ n, xs n) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (⋃ n, xs n) := by
      simp [e_pow2, Set.singleton_subset_iff, hk]
    obtain ⟨m, hm, hkm⟩ := hchar.mp hfin
    have hwit : ∀ i ∈ e m, ∃ n, i ∈ xs n := by
      intro i hi
      obtain ⟨n, hix⟩ := Set.mem_iUnion.mp (hm hi)
      exact ⟨n, hix⟩
    obtain ⟨s, hs⟩ := (e_finite m).exists_finset_coe
    obtain ⟨N, hN⟩ := exists_index_of_finset xs hmono s (fun i hi =>
      hwit i (by
        have : i ∈ (s : Set ℕ) := hi
        rwa [hs] at this))
    have hem : e m ⊆ xs N := by rwa [← hs]
    refine Set.mem_iUnion.mpr ⟨N, ?_⟩
    have : e (2 ^ k) ⊆ f (xs N) :=
      subset_trans hkm (isScottContinuous_monotone hf hem)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro k hk
    obtain ⟨n, hkn⟩ := Set.mem_iUnion.mp hk
    exact isScottContinuous_monotone hf (Set.subset_iUnion xs n) hkn

end DomainTheory.DataTypesAsLattices
