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































theorem union_left_isScottContinuous (c : Pomega) :
    IsScottContinuous (fun x => x ∪ c) := by
  intro x
  ext k
  constructor
  · intro hk
    rcases hk with hk | hk
    · have : k ∈ scottUnion (fun z => z) x := by
        rw [← id_isScottContinuous x]; exact hk
      obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
      exact mem_scottUnion.mpr ⟨n, hn, Or.inl hkn⟩
    · exact mem_scottUnion.mpr ⟨0, by simp [e_zero], Or.inr hk⟩
  · intro hk
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp hk
    rcases hkn with hkn | hkn
    · exact Or.inl (isScottContinuous_monotone id_isScottContinuous hn hkn)
    · exact Or.inr hkn

end DomainTheory.DataTypesAsLattices
