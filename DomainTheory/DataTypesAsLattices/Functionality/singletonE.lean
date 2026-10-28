
module

public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def singletonE (a : Pomega) : RestrictedEquiv where
  rel := fun x y => x = a ∧ y = a
  symm := by
    intro x y ⟨hx, hy⟩
    exact ⟨hy, hx⟩
  trans := by
    intro x y z ⟨hx, _hy⟩ ⟨_hy', hz⟩
    exact ⟨hx, hz⟩

end DomainTheory.DataTypesAsLattices
