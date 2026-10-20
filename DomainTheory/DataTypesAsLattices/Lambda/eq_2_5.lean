/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Embedding
import DomainTheory.DataTypesAsLattices.Lambda.Basic


namespace DomainTheory.DataTypesAsLattices























/-- **Scott 1976, (2.5).** `(6 ∪ 10) + 1 = 7 ∪ 11`. -/
theorem eq_2_5 : succSet (ofNat 6 ∪ ofNat 10) = ofNat 7 ∪ ofNat 11 := by
  ext k
  constructor
  · intro ⟨n, hn, hk⟩
    rcases hn with h6 | h10
    · simp [ofNat] at h6; subst h6; simp [ofNat, hk]
    · simp [ofNat] at h10; subst h10; simp [ofNat, hk]
  · intro hk
    rcases hk with h7 | h11
    · simp [ofNat] at h7; exact ⟨6, Or.inl (by simp [ofNat]), by simp [h7]⟩
    · simp [ofNat] at h11; exact ⟨10, Or.inr (by simp [ofNat]), by simp [h11]⟩

end DomainTheory.DataTypesAsLattices
