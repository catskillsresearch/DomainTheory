module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def evalC : Pomega :=
  graph (fun u => funOf (funOf u (ofNat 0)) (funOf u (ofNat 1)))

end DomainTheory.DataTypesAsLattices
