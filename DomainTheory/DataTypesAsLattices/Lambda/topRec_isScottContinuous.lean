/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices





























theorem topRec_isScottContinuous : IsScottContinuous topRec := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | ⟨n, hn, rfl⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl hk⟩
    · exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inr ⟨n, by simp [e_pow2], rfl⟩⟩
  · intro hk
    obtain ⟨m, hm, hkm⟩ := mem_scottUnion.mp hk
    rcases hkm with hk | ⟨n, hn, rfl⟩
    · exact Or.inl hk
    · exact Or.inr ⟨n, hm hn, rfl⟩

end DomainTheory.DataTypesAsLattices
