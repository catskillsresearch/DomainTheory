/-ai
Scott 1976, (7.4). The restricted equivalence of a retract a relates x to y exactly when both are typed by a and they are equal. Symmetry swaps the typing hypotheses and reverses the equality. Transitivity keeps the typing of the outer elements and composes the equalities.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (7.4).** Identity relation on the range of a retract. -/
def Ea (a : Pomega) : RestrictedEquiv where
  rel := fun x y => typed x a ∧ typed y a ∧ x = y
  symm := by
    intro x y ⟨hx, hy, h⟩
    exact ⟨hy, hx, h.symm⟩
  trans := by
    intro x y z ⟨hx, hy, hxy⟩ ⟨_, hz, hyz⟩
    exact ⟨hx, hz, hxy.trans hyz⟩

end DomainTheory.DataTypesAsLattices
