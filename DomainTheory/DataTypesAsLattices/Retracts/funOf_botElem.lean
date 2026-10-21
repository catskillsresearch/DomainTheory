/-ai
Applying the empty set to any element returns the empty set.

Extensionality and the definitions of application and of the empty set give the equality.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem funOf_botElem (x : Pomega) : funOf botElem x = botElem := by
  ext m
  simp [funOf, botElem]

end DomainTheory.DataTypesAsLattices
