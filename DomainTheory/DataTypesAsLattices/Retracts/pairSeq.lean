module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.21) / (4.2).** Pairing as a distributive sequence. -/
def pairSeq (x y : Pomega) : Pomega := seq2 x y

end DomainTheory.DataTypesAsLattices
