
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def hZero : Pomega := funOf inleftC (ofNat 0)

end DomainTheory.DataTypesAsLattices
