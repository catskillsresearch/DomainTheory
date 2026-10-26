module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Lambda.condSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def seq1 (x : Pomega) : Pomega :=
  graph (fun z => condSet z x botElem)

end DomainTheory.DataTypesAsLattices
