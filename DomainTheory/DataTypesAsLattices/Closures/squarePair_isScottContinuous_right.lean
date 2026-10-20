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































theorem squarePair_isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => squarePair x y) := by
  intro y
  ext k
  constructor
  · intro hk
    rcases hk with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inl ⟨n, hn, hk⟩⟩
    · exact mem_scottUnion.mpr ⟨2 ^ m, by simp [e_pow2, Set.singleton_subset_iff, hm],
        Or.inr ⟨m, by simp [e_pow2], hk⟩⟩
  · intro hk
    obtain ⟨p, hp, hkp⟩ := mem_scottUnion.mp hk
    rcases hkp with ⟨n, hn, hk⟩ | ⟨m, hm, hk⟩
    · exact Or.inl ⟨n, hn, hk⟩
    · exact Or.inr ⟨m, hp hm, hk⟩

end DomainTheory.DataTypesAsLattices
