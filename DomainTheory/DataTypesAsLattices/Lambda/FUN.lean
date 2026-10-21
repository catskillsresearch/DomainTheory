/-ai
Scott's section 2 defines the subspace FUN of graphs to be the set of those u that equal the graph of their own application.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, §2.** The subspace `FUN` of graphs. -/
def FUN : Set Pomega := {u | u = graph (funOf u)}

end DomainTheory.DataTypesAsLattices
