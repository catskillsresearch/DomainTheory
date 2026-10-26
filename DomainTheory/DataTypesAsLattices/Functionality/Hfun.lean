module

public import DomainTheory.DataTypesAsLattices.FixedPoint.fix
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm
public import DomainTheory.DataTypesAsLattices.Functionality.HF

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Raw least fixed point of the (4.43) operator. -/
def Hfun : Pomega := fix HF

end DomainTheory.DataTypesAsLattices
