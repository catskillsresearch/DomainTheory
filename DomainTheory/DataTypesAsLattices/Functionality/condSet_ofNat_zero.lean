/-ai
The conditional set of the numeral 0, with branches x and y, equals x.

Membership extensionality and the definitions of the conditional set and of the numeral give the equality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condSet_ofNat_zero (x y : Pomega) : condSet (ofNat 0) x y = x := by
  ext n
  simp [condSet, ofNat]

end DomainTheory.DataTypesAsLattices
