module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.22).** Longer sequences by cons. -/
def seqCons (x xs : Pomega) : Pomega :=
  graph (fun z => condSet z x (funOf xs (predSet z)))

end DomainTheory.DataTypesAsLattices
