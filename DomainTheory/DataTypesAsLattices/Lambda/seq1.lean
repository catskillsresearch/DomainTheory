/-ai
The one-element sequence of a set is the graph of the conditional that returns that set on zero and the bottom element otherwise.
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

def seq1 (x : Pomega) : Pomega :=
  graph (fun z => condSet z x botElem)

end DomainTheory.DataTypesAsLattices
