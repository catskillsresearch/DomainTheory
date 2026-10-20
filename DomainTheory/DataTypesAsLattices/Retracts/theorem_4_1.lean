/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_sUnion
import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directedSubset


namespace DomainTheory.DataTypesAsLattices






































/-- **Scott 1976, Theorem 4.1 (The lattice theorem).**
Fixed points of a continuous function form a complete lattice under `⊆`;
those of a retract form a continuous lattice. -/
theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints f ∧
        lfpAbove f (⋃₀ A) ∈ Fixpoints f) ∧
      ∀ {a} (_ha : IsRetract a),
        Fixpoints (funOf a) = {x | typed x a} ∧
          ∀ x : Fixpoints (funOf a),
            IsDirectedSubset (retractBasis a x) ∧
              (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) := by
  constructor
  · intro A hA
    exact ⟨theorem_4_1_complete f hf A hA, lfpAbove_mem hf hA⟩
  · intro a ha
    constructor
    · ext x
      simp [Fixpoints, typed, eq_comm]
    · intro x
      exact ⟨retractBasis_directedSubset ha x, retractBasis_sUnion ha x⟩

end DomainTheory.DataTypesAsLattices
