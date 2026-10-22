
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.expPayload

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def hVar (e t : Pomega) : Pomega := funOf t (expPayload e)

end DomainTheory.DataTypesAsLattices
