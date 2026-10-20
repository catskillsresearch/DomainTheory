/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_inj
import DomainTheory.DataTypesAsLattices.Functionality.typed_pairSeq_tensorR


namespace DomainTheory.DataTypesAsLattices






















/-- **Scott 1976, Theorem 7.2 (iii).** `E_{a ⊗ b}` agrees with
`E_a × E_b` on `pairSeq` elements. -/
theorem theorem_7_2_iii (a b x y x' y' : Pomega) :
    (Ea (tensorR a b)).rel (pairSeq x y) (pairSeq x' y') ↔
      (prodE (Ea a) (Ea b)).rel (pairSeq x y) (pairSeq x' y') := by
  constructor
  · intro ⟨hu, hv, heq⟩
    obtain ⟨rfl, rfl⟩ := pairSeq_inj heq
    have hxy : typed x a ∧ typed y b := (typed_pairSeq_tensorR a b x y).mp hu
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pairSeq_app_zero, pairSeq_app_one]; rfl
    · rw [pairSeq_app_zero, pairSeq_app_one]; rfl
    · rw [pairSeq_app_zero]
      exact ⟨hxy.1, hxy.1, rfl⟩
    · rw [pairSeq_app_one]
      exact ⟨hxy.2, hxy.2, rfl⟩
  · intro ⟨_hu, _hv, h0, h1⟩
    rw [pairSeq_app_zero, pairSeq_app_zero] at h0
    rw [pairSeq_app_one, pairSeq_app_one] at h1
    rcases h0 with ⟨hx, hx', heqx⟩
    rcases h1 with ⟨hy, hy', heqy⟩
    refine ⟨(typed_pairSeq_tensorR a b x y).mpr ⟨hx, hy⟩,
      (typed_pairSeq_tensorR a b x' y').mpr ⟨hx', hy'⟩, ?_⟩
    rw [heqx, heqy]

end DomainTheory.DataTypesAsLattices
