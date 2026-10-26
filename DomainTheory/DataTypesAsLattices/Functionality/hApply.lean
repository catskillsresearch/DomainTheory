module

public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- Recursive call of a candidate `ℋ` on a subexpression. -/
def hApply (H e t : Pomega) : Pomega := funOf (funOf H e) t

end DomainTheory.DataTypesAsLattices
