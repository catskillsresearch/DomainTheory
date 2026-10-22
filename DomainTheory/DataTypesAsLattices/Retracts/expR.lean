module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.expF

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.44).** `exp` as the least fixed point of the seven-tag
syntax functor. -/
def expR : Pomega := funOf Ycomb (graph expF)

end DomainTheory.DataTypesAsLattices
