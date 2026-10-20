module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.28).** Left projection of a tagged sum. -/
def outleftC : Pomega :=
  graph (fun u => condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem)

end DomainTheory.DataTypesAsLattices
