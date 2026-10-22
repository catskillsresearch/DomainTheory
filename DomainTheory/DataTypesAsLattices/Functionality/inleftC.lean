
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.26).** Left injection. -/
def inleftC : Pomega := graph (fun x => pairSeq (ofNat 0) x)

end DomainTheory.DataTypesAsLattices
