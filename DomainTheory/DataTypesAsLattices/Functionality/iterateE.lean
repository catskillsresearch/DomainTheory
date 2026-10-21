/-ai
The restricted equivalence iterateE f x is the identity on the orbit of the iterates Z n f x: u is related to v when u equals some iterate and u equals v. Symmetry transports the orbit witness along the equality, and transitivity keeps the witness from the first link and composes the equalities.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.Z

@[expose] public section

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
