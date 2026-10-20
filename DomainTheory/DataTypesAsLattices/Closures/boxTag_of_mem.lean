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































theorem boxTag_of_mem {x : Pomega} {m : ℕ} (hm : m ∈ x) (i : ℕ) :
    boxTag i x = ofNat i := by
  ext n
  simp only [boxTag, condSet, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨hn, _⟩ | ⟨hn, _⟩) <;> exact hn
  · intro hn
    cases m with
    | zero => exact Or.inl ⟨hn, hm⟩
    | succ k => exact Or.inr ⟨hn, k, hm⟩

end DomainTheory.DataTypesAsLattices
