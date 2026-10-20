module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.IsDirectedSubset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Compactness of a fixed point under subset, without a lattice instance. -/
def IsCompactSubset {f : Pomega → Pomega} (x : Fixpoints f) : Prop :=
  ∀ s : Set (Fixpoints f),
    IsDirectedSubset s →
      (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
      ∃ z ∈ s, (x : Pomega) ⊆ z

end DomainTheory.DataTypesAsLattices
