/-ai
The tag of a seven-sum abstract-syntax code is its application at the numeral 0.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Tag and payload of a seven-sum abstract-syntax code. -/
def expTag (e : Pomega) : Pomega := funOf e (ofNat 0)

end DomainTheory.DataTypesAsLattices
