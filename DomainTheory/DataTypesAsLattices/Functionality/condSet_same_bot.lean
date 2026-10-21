/-ai
The conditional set of bottom with both branches equal to x is bottom.

This is the bottom rule for the conditional set applied to x and x.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.condSet_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem condSet_same_bot (x : Pomega) : condSet botElem x x = botElem :=
  condSet_bot x x

end DomainTheory.DataTypesAsLattices
