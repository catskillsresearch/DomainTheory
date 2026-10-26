
module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def Fofg (g : Pomega → Pomega → Pomega) (f : Pomega) : Pomega :=
  graph (fun x => g x (funOf f x))

end DomainTheory.DataTypesAsLattices
