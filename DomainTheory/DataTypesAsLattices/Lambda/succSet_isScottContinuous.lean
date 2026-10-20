/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices









theorem succSet_isScottContinuous : IsScottContinuous succSet := by
  intro x
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    refine mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn], ?_⟩
    exact ⟨n, by simp [e_pow2], hk⟩
  · intro hk
    obtain ⟨m, hm, n, hn, hk⟩ := mem_scottUnion.mp hk
    exact ⟨n, hm hn, hk⟩

end DomainTheory.DataTypesAsLattices
