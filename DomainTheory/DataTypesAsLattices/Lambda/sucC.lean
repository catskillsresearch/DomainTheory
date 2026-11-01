module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Lambda.succSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def sucC : Pomega := graph succSet

end DomainTheory.DataTypesAsLattices
