/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices


























theorem sigmaJ_isScottContinuous (j : ℕ) : IsScottContinuous (sigmaJ j) := by
  intro x
  ext p
  constructor
  · intro ⟨k, heq, hp⟩
    refine mem_scottUnion.mpr ⟨2 ^ pair j k, ?_, k, heq, ?_⟩
    · simpa [e_pow2, Set.singleton_subset_iff] using hp
    · simp [e_pow2]
  · intro hp
    obtain ⟨n, hn, k, heq, hpk⟩ := mem_scottUnion.mp hp
    exact ⟨k, heq, hn hpk⟩

end DomainTheory.DataTypesAsLattices
