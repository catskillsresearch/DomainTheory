/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices









theorem predSet_isScottContinuous : IsScottContinuous predSet := by
  intro x
  ext k
  constructor
  · intro hk
    refine mem_scottUnion.mpr ⟨2 ^ (k + 1), ?_, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff, predSet] using hk
    · simp [predSet, e_pow2]
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    exact hm hkm

end DomainTheory.DataTypesAsLattices
