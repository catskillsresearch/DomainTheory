module

public import DomainTheory.DataTypesAsLattices.Lambda.Ycomb
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.expF

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def expR : Pomega := funOf Ycomb (graph expF)

end DomainTheory.DataTypesAsLattices
