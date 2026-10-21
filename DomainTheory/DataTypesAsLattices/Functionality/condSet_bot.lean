/-ai
The conditional set of the bottom element, with any two branches, is bottom.

Membership extensionality and the definitions of the conditional set and of bottom give the equality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



theorem condSet_bot (x y : Pomega) : condSet botElem x y = botElem := by
  ext n
  simp [condSet, botElem]

end DomainTheory.DataTypesAsLattices
