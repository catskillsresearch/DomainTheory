module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.29).** Right projection of a tagged sum. -/
def outrightC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) botElem (funOf u (ofNat 1)))

end DomainTheory.DataTypesAsLattices
