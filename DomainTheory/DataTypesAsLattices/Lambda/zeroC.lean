/-ai
The zero combinator is the numeral 0.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def zeroC : Pomega := ofNat 0

end DomainTheory.DataTypesAsLattices
