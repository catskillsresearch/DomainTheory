/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic
import DomainTheory.DataTypesAsLattices.Lambda.seqShift_app


namespace DomainTheory.DataTypesAsLattices








































theorem seqShift_ofNat (u : Pomega) (i : ℕ) :
    funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
  rw [seqShift_app]
  ext m
  constructor
  · intro hm
    obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
    simp [succSet, ofNat] at hj; subst hj; exact hmj
  · intro hm
    exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩

end DomainTheory.DataTypesAsLattices
