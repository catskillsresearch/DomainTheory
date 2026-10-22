
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 7.2 (i).** `E_a` is the identity on the range of `a`. -/
theorem theorem_7_2_i (a x y : Pomega) :
    (Ea a).rel x y ↔ typed x a ∧ typed y a ∧ x = y :=
  Iff.rfl

end DomainTheory.DataTypesAsLattices
