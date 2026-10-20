/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices



































theorem openR_map_isScottContinuous :
    IsScottContinuous (fun u => {m | ∃ n, e n ⊆ e m ∧ n ∈ u}) := by
  intro u
  ext m
  constructor
  · intro ⟨n, hn, hnu⟩
    exact mem_scottUnion.mpr ⟨2 ^ n, by simp [e_pow2, Set.singleton_subset_iff, hnu],
      ⟨n, hn, by simp [e_pow2]⟩⟩
  · intro hm
    obtain ⟨k, hk, n, hn, hnk⟩ := mem_scottUnion.mp hm
    exact ⟨n, hn, hk hnk⟩

end DomainTheory.DataTypesAsLattices
