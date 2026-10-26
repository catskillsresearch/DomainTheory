module

public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.lambF

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def lambR : Pomega := funOf Ycomb (graph lambF)

end DomainTheory.DataTypesAsLattices
