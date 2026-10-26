
module

public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.inleftC

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def hZero : Pomega := funOf inleftC (ofNat 0)

end DomainTheory.DataTypesAsLattices
