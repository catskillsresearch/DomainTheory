/-ai
The graph associated with a binary map g at an element f is the graph of the map sending x to g at x and at the application of f to x.
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

def Fofg (g : Pomega → Pomega → Pomega) (f : Pomega) : Pomega :=
  graph (fun x => g x (funOf f x))

end DomainTheory.DataTypesAsLattices
