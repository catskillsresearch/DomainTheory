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
