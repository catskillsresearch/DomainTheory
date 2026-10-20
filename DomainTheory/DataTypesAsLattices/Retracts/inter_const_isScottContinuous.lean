/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic


namespace DomainTheory.DataTypesAsLattices





















theorem inter_const_isScottContinuous {f : Pomega → Pomega}
    (hf : IsScottContinuous f) (b : Pomega) :
    IsScottContinuous (fun z => f z ∩ b) := by
  intro x
  ext k
  constructor
  · intro ⟨hkf, hkb⟩
    have : k ∈ scottUnion f x := by rwa [← hf x]
    obtain ⟨n, hn, hkn⟩ := mem_scottUnion.mp this
    exact mem_scottUnion.mpr ⟨n, hn, hkn, hkb⟩
  · intro hk
    obtain ⟨n, hn, hkn, hkb⟩ := mem_scottUnion.mp hk
    exact ⟨isScottContinuous_monotone hf hn hkn, hkb⟩

end DomainTheory.DataTypesAsLattices
