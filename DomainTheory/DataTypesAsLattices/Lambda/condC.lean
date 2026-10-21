/-ai
The conditional combinator is the graph of the curried McCarthy conditional, sending x and y and z to the conditional of z, x, and y.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.condSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def condC : Pomega :=
  graph (fun x => graph (fun y => graph (fun z => condSet z x y)))

end DomainTheory.DataTypesAsLattices
