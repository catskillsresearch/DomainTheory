/-ai
The integer retract sends the bottom element to the bottom element.

Rewrite the application by the application law for the integer retract, then use that the doubly strict conditional on the bottom element is the bottom element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic
public import DomainTheory.DataTypesAsLattices.Retracts.intR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices














































theorem intR_bot : funOf intR botElem = botElem := by
  rw [intR_app, dcondSet_bot]

end DomainTheory.DataTypesAsLattices
