module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.dollarStepBody

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def dollarStep (s : Pomega) : Pomega :=
  graph (fun u => graph (fun z => dollarStepBody s u z))

end DomainTheory.DataTypesAsLattices
