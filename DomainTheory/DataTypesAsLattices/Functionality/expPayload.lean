/-ai
The payload of an abstract-syntax code is its application at the numeral 1.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

def expPayload (e : Pomega) : Pomega := funOf e (ofNat 1)

end DomainTheory.DataTypesAsLattices
