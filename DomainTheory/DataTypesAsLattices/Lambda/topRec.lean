module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.16).** `⊤ = Y(λx. 0 ∪ (x + 1))`. -/
def topRec (x : Pomega) : Pomega := ofNat 0 ∪ succSet x

end DomainTheory.DataTypesAsLattices
