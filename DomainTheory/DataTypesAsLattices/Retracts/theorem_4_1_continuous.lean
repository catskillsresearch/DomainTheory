/-ai
Scott 1976, Theorem 4.1, the continuous-lattice half. For a retract, the finite-image basis of each fixed point is a directed subset, the point is the union of the underlying sets of the basis, and every basis element lies below some member of any directed subset of fixed points whose underlying union lies above the point. The statement uses subset directedness so that the type does not mention a complete-lattice instance.

Directedness and the union equation are the corresponding basis lemmas. A basis element comes from a finite set e n contained in the point, so that finite set is contained in the underlying union of the directed subset. The subset is a directed set, and the finite-cover lemma supplies a member containing e n. Monotonicity of application together with that member's fixed-point equation puts the basis element below the member.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.directed_finite_cover
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_sUnion
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directedSubset

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.1, continuous-lattice half.**
The finite-image points form a directed way-below basis for every point in
the range of a retract. Stated with subset directedness so the compared
type does not mention a `CompleteLattice` instance. -/
theorem theorem_4_1_continuous {a : Pomega} (ha : Retract a) :
    ∀ x : Fixpoints (funOf a),
      DirectedSubset (retractBasis a x) ∧
        (x : Pomega) = ⋃₀ (Subtype.val '' retractBasis a x) ∧
        ∀ y ∈ retractBasis a x,
          ∀ s : Set (Fixpoints (funOf a)),
            DirectedSubset s →
              (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
              ∃ z ∈ s, (y : Pomega) ⊆ z := by
  intro x
  refine ⟨retractBasis_directedSubset ha x, retractBasis_sUnion ha x, ?_⟩
  intro y hy s hs hxs
  obtain ⟨n, hnx, hyn⟩ := hy
  have hen : e n ⊆ ⋃₀ (Subtype.val '' s) := hnx.trans hxs
  have hs' : DirectedSet s :=
    ⟨⟨hs.out.1, fun u hu v hv => by
      obtain ⟨w, hw, huw, hvw⟩ := hs.out.2 hu hv
      exact ⟨w, hw, huw, hvw⟩⟩⟩
  obtain ⟨z, hz, hnz⟩ :=
    directed_finite_cover hs' (e_finite n) (by simpa [Fixpoints.vals] using hen)
  refine ⟨z, hz, ?_⟩
  rw [hyn]
  have := isScottContinuous_monotone (funOf_isScottContinuous a) hnz
  rwa [z.property] at this

end DomainTheory.DataTypesAsLattices
