/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import Mathlib.Data.Set.Finite.Powerset
import DomainTheory.DataTypesAsLattices.Classification.Basic
import DomainTheory.DataTypesAsLattices.Classification.theorem_6_1


namespace DomainTheory.DataTypesAsLattices

open TopologicalSpace








































































































/-- **Scott 1976, Table 3 / Theorem 6.1.** `𝔊` is the class of continuous
preimages of the typical open set `{x | 0 ∈ x}`. -/
theorem typicalG_universal (U : Set Pomega) :
    IsScottOpen U ↔ ∃ f, IsScottContinuous f ∧ U = {x | f x ∈ typicalG} := by
  constructor
  · intro hU
    obtain ⟨f, hf, rfl⟩ := (theorem_6_1).2 U hU
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact (theorem_6_1).1 f hf

end DomainTheory.DataTypesAsLattices
