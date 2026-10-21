/-ai
Scott 1976, (2.24)–(2.25): revaluation of a functional along a set, as a distributive sequence, is the union of the applications of the functional to the numerals of the indices that belong to the set.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.24)–(2.25).** Revaluation as a distributive sequence. -/
def seqFun (u x : Pomega) : Pomega :=
  ⋃ i ∈ x, funOf u (ofNat i)

end DomainTheory.DataTypesAsLattices
