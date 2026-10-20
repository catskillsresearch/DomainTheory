module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.seqFun

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def dollarC : Pomega :=
  graph (fun u => graph (fun x => seqFun u x))

end DomainTheory.DataTypesAsLattices
