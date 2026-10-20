module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.30).** Tag of a summand; same combinator as `fst`. -/
def whichC : Pomega := fstC

end DomainTheory.DataTypesAsLattices
