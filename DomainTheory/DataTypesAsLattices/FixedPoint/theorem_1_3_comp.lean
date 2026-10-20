/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Graph
import DomainTheory.DataTypesAsLattices.FixedPoint.Basic


namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, Theorem 1.3, composition.** -/
theorem theorem_1_3_comp {f g : Pomega → Pomega}
    (hf : IsScottContinuous f) (hg : IsScottContinuous g) :
    IsScottContinuous (f ∘ g) := by
  intro x
  ext k
  constructor
  · intro hk
    have hk' : k ∈ f (g x) := hk
    have := (theorem_1_1 f).mp hf (g x) (2 ^ k)
    have hfin : e (2 ^ k) ⊆ f (g x) := by
      simpa [e_pow2, Set.singleton_subset_iff] using hk'
    obtain ⟨m, hm, hkm⟩ := this.mp hfin
    have := (theorem_1_1 g).mp hg x m
    obtain ⟨n, hn, hmn⟩ := this.mp hm
    refine mem_scottUnion.mpr ⟨n, hn, ?_⟩
    have : e (2 ^ k) ⊆ f (g (e n)) :=
      subset_trans hkm (isScottContinuous_monotone hf hmn)
    simpa [e_pow2, Set.singleton_subset_iff] using this
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    exact isScottContinuous_monotone hf (isScottContinuous_monotone hg hn) hkn

end DomainTheory.DataTypesAsLattices
