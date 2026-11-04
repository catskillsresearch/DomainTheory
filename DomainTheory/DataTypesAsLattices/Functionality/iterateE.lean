module

public import DomainTheory.DataTypesAsLattices.Enumeration.Zcomb

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def iterateE (f x : Pomega) : RestrictedEquiv where
  rel := fun u v => (∃ n, u = Z n f x) ∧ u = v
  symm := by
    intro u v ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro u v w ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

end DomainTheory.DataTypesAsLattices
