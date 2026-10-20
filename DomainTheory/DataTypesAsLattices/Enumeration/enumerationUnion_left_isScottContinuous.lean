/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices































































theorem enumerationUnion_left_isScottContinuous (y : Pomega) :
    IsScottContinuous (fun x => x ∪ y) := by
  intro x
  ext n
  constructor
  · rintro (hn | hn)
    · exact mem_scottUnion.mpr ⟨2 ^ n,
        by simp [e_pow2, Set.singleton_subset_iff, hn],
        Or.inl (by simp [e_pow2])⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hn⟩
  · intro hn
    obtain ⟨i, hi, hni⟩ := mem_scottUnion.mp hn
    exact hni.elim (fun h => Or.inl (hi h)) Or.inr

end DomainTheory.DataTypesAsLattices
