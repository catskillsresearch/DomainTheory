
module

public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §2.** The subspace `FUN` of graphs. -/
def FUN : Set Pomega := {u | u = graph (funOf u)}

end DomainTheory.DataTypesAsLattices
