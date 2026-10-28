module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.mem

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Nrel : RestrictedEquiv where
  rel := fun x y => (∃ n, x = ofNat n) ∧ x = y
  symm := by
    intro x y ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro x y z ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

end DomainTheory.DataTypesAsLattices
