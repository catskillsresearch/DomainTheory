module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Directedness of fixed points under subset, without a lattice instance. -/
class DirectedSubset {f : Pomega → Pomega} (s : Set (Fixpoints f)) : Prop where
  out : s.Nonempty ∧
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s →
      ∃ z ∈ s, (x : Pomega) ⊆ z ∧ (y : Pomega) ⊆ z

end DomainTheory.DataTypesAsLattices
