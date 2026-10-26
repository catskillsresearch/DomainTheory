
module

public import DomainTheory.DataTypesAsLattices.Retracts.sndC
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.31).** Untagged payload; same combinator as `snd`. -/
def outC : Pomega := sndC

end DomainTheory.DataTypesAsLattices
