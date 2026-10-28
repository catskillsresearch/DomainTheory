module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.lambR

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def envR : Pomega :=
  graph (fun t => graph (fun n => funOf lambR (funOf t n)))

end DomainTheory.DataTypesAsLattices
