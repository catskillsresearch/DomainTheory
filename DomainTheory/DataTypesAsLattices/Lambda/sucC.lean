/-ai
The successor combinator is the graph of the successor operation on subsets of the natural numbers.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.succSet

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def sucC : Pomega := graph succSet

end DomainTheory.DataTypesAsLattices
