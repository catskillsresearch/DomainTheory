/-ai
Scott 1976, (2.21) and (4.2). Pairing of two sets is the two-place distributive sequence on those sets.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (2.21) / (4.2).** Pairing as a distributive sequence. -/
def pairSeq (x y : Pomega) : Pomega := seq2 x y

end DomainTheory.DataTypesAsLattices
