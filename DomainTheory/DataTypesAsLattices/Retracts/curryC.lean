module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def curryC : Pomega :=
  graph (fun u => graph (fun x => graph (fun y => funOf u (pairSeq x y))))

end DomainTheory.DataTypesAsLattices
