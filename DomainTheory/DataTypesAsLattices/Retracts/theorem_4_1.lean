/-ai
Scott 1976, Theorem 4.1, the lattice theorem. The fixed points of a Scott-continuous map are closed under the greatest fixed point below an intersection and the least fixed point above a union. For a retract, the fixed points of its application are exactly the sets it types, and each such fixed point is the union of a directed finite-image basis.

The closure claims are the complete-lattice half of the theorem and the membership lemma for least fixed points above a union. For a retract, the fixed-point and typing predicates agree by unfolding and symmetry of equality. Directedness of the basis and the union equation are the corresponding basis lemmas.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_sUnion
public import DomainTheory.DataTypesAsLattices.Retracts.retractBasis_directedSubset

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 4.1 (The lattice theorem).**
Fixed points of a continuous function form a complete lattice under `⊆`;
those of a retract form a continuous lattice. -/
theorem theorem_4_1 {f : Pomega → Pomega} (hf : IsScottContinuous f) :
    (∀ A : Set Pomega, A ⊆ Fixpoints f →
      gfpBelow f (⋂₀ A) ∈ Fixpoints f ∧
        lfpAbove f (⋃₀ A) ∈ Fixpoints f) ∧
      ∀ {a} (_ha : Retract a),
        Fixpoints (funOf a) = {x | typed x a} ∧
          ∀ x : Fixpoints (funOf a),
            DirectedSubset (retractBasis a x) ∧
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
