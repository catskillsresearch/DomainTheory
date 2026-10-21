/-ai
The expression retract is the application of the Y combinator to the graph of the abstract-syntax functor, the least fixed point of that functor in Scott's formula (4.44).
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.expF

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.44).** `exp` as the least fixed point of the seven-tag
syntax functor. -/
def expR : Pomega := funOf Ycomb (graph expF)

end DomainTheory.DataTypesAsLattices
