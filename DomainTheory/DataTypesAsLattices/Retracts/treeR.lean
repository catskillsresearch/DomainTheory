module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def treeR : Pomega := funOf Ycomb (graph treeF)

end DomainTheory.DataTypesAsLattices
