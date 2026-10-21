/-ai
The dollar combinator is the graph of the map sending a sequence u to the graph of x ↦ seq(u)(x).
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def dollarC : Pomega :=
  graph (fun u => graph (fun x => seqFun u x))

end DomainTheory.DataTypesAsLattices
