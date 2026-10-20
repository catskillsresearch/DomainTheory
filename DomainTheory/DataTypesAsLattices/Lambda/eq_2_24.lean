/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.seqShift_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices








































/-- **Scott 1976, (2.24).** `seq(u)(x) = x ⊃ u_0, seq(λt. u_{t+1})(x−1)`. -/
theorem eq_2_24 (u x : Pomega) :
    seqFun u x =
      condSet x (funOf u (ofNat 0))
        (seqFun (seqShift u) (predSet x)) := by
  ext k
  constructor
  · intro hk
    obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hk
    cases i with
    | zero => exact Or.inl ⟨hki, hi⟩
    | succ i =>
      refine Or.inr ⟨?_, i, hi⟩
      refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
      have : funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
        rw [seqShift_app]
        ext m
        constructor
        · intro hm
          obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
          simp [succSet, ofNat] at hj; subst hj; exact hmj
        · intro hm
          exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩
      simpa [this] using hki
  · intro hk
    rcases hk with ⟨hk0, h0x⟩ | ⟨hpos, t, ht⟩
    · exact Set.mem_iUnion₂.mpr ⟨0, h0x, hk0⟩
    · obtain ⟨i, hi, hki⟩ := Set.mem_iUnion₂.mp hpos
      have : funOf (seqShift u) (ofNat i) = funOf u (ofNat (i + 1)) := by
        rw [seqShift_app]
        ext m
        constructor
        · intro hm
          obtain ⟨j, hj, hmj⟩ := Set.mem_iUnion₂.mp hm
          simp [succSet, ofNat] at hj; subst hj; exact hmj
        · intro hm
          exact Set.mem_iUnion₂.mpr ⟨i + 1, ⟨i, rfl, rfl⟩, hm⟩
      refine Set.mem_iUnion₂.mpr ⟨i + 1, hi, ?_⟩
      simpa [this] using hki

end DomainTheory.DataTypesAsLattices
