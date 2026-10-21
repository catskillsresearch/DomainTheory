/-ai
Scott 1976, (4.31). The untagged-payload combinator is the second projection.
ai-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.31).** Untagged payload; same combinator as `snd`. -/
def outC : Pomega := sndC

end DomainTheory.DataTypesAsLattices
