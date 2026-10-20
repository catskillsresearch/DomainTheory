module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Z

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- The identity on the orbit `{fⁿ(x) | n ∈ ω}`. -/
def iterateE (f x : Pomega) : RestrictedEquiv where
  rel := fun u v => (∃ n, u = Z n f x) ∧ u = v
  symm := by
    intro u v ⟨hn, h⟩
    exact ⟨by rw [← h]; exact hn, h.symm⟩
  trans := by
    intro u v w ⟨hn, hxy⟩ ⟨_, hyz⟩
    exact ⟨hn, hxy.trans hyz⟩

end DomainTheory.DataTypesAsLattices
