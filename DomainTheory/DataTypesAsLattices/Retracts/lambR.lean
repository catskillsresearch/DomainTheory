/-ai
The lambda retract is the application of the Y combinator to the graph of the lambda functor.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.lambF

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def lambR : Pomega := funOf Ycomb (graph lambF)

end DomainTheory.DataTypesAsLattices
