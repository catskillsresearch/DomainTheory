module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Term-level shift `λt. u(t+1)`, which agrees with `seqShift` on numerals. -/
def termShift (u : Pomega) : Pomega :=
  graph (fun t => funOf u (succSet t))

end DomainTheory.DataTypesAsLattices
