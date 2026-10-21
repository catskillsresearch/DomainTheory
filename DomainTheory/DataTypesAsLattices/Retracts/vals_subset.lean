/-ai
The values of a set of fixed points of a map on Pω are themselves fixed points of that map.

A value in the image is the underlying element of some fixed-point subtype, and the subtype property is the fixed-point property.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.Retracts.vals

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

theorem Fixpoints.vals_subset {f : Pomega → Pomega} (A : Set (Fixpoints f)) :
    Fixpoints.vals A ⊆ Fixpoints f := by
  intro x hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.property

end DomainTheory.DataTypesAsLattices
