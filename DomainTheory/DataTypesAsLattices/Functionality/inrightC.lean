
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.RestrictedEquiv
public import DomainTheory.DataTypesAsLattices.Functionality.LambTerm

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.27).** Right injection. -/
def inrightC : Pomega := graph (fun x => pairSeq (ofNat 1) x)

end DomainTheory.DataTypesAsLattices
