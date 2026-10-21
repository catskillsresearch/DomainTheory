/-ai
The predecessor combinator is the graph of the predecessor operation.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.predSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def predC : Pomega := graph predSet

end DomainTheory.DataTypesAsLattices
