/-ai
A fixed point is compact for inclusion when every directed set of fixed points whose union of values contains it already has some member whose value contains it.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.IsDirectedSubset

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Compactness of a fixed point under subset, without a lattice instance. -/
def IsCompactSubset {f : Pomega → Pomega} (x : Fixpoints f) : Prop :=
  ∀ s : Set (Fixpoints f),
    IsDirectedSubset s →
      (x : Pomega) ⊆ ⋃₀ (Subtype.val '' s) →
      ∃ z ∈ s, (x : Pomega) ⊆ z

end DomainTheory.DataTypesAsLattices
