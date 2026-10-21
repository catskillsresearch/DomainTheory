/-ai
Scott 1976, (2.19)–(2.21): the empty finite sequence, regarded as a distributive function, is the bottom element.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Term
public import DomainTheory.DataTypesAsLattices.Lambda.IsCombinatory
public import DomainTheory.DataTypesAsLattices.Lambda.Comb
public import DomainTheory.DataTypesAsLattices.Lambda.mem_ofNat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.19)–(2.21).** Finite sequences as distributive functions. -/
def seq0 : Pomega := botElem

end DomainTheory.DataTypesAsLattices
