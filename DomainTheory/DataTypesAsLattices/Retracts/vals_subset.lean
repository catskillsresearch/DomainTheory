module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.vals

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem Fixpoints.vals_subset {f : Pomega → Pomega} (A : Set (Fixpoints f)) :
    Fixpoints.vals A ⊆ Fixpoints f := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

end DomainTheory.DataTypesAsLattices
