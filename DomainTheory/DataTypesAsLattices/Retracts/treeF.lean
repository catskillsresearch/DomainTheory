/-ai
Scott 1976, (4.38). The tree functor sends a retract z to the sum of the bottom element with the product of z with itself.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.38).** The tree functor. -/
def treeF (z : Pomega) : Pomega := plusR botElem (tensorR z z)

end DomainTheory.DataTypesAsLattices
