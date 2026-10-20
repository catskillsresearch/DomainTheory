/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.directed_finite_cover
import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_sUnion
import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directedSubset


namespace DomainTheory.DataTypesAsLattices






































/-- **Scott 1976, Theorem 4.1, continuous-lattice half.**
The finite-image points form a directed way-below basis for every point in
the range of a retract. Stated with subset directedness so the compared
type does not mention a `CompleteLattice` instance. -/
theorem theorem_4_1_continuous {a : Pomega} (ha : IsRetract a) :
    ∀ x : Fixpoints (funOf a),
      IsDirectedSubset (retractBasis a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) ∧
        ∀ y ∈ retractBasis a x,
          ∀ s : Set (Fixpoints (funOf a)),
            IsDirectedSubset s →
              (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
              ∃ z ∈ s, (y : Pomega) ⊆ z := by
  intro x
  refine ⟨retractBasis_directedSubset ha x, retractBasis_sUnion ha x, ?_⟩
  intro y hy s hs hxs
  obtain ⟨n, hnx, hyn⟩ := hy
  have hen : e n ⊆ ⋃₀ (Subtype.val '' s) := hnx.trans hxs
  have hs' : IsDirectedSet s :=
    ⟨hs.1, fun u hu v hv => by
      obtain ⟨w, hw, huw, hvw⟩ := hs.2 hu hv
      exact ⟨w, hw, huw, hvw⟩⟩
  obtain ⟨z, hz, hnz⟩ :=
    directed_finite_cover hs' (e_finite n) (by simpa [Fixpoints.vals] using hen)
  refine ⟨z, hz, ?_⟩
  rw [hyn]
  have := isScottContinuous_monotone (funOf_isScottContinuous a) hnz
  rwa [z.property] at this

end DomainTheory.DataTypesAsLattices
