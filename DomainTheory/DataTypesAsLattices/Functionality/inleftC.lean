
module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.26).** Left injection. -/
def inleftC : Pomega := graph (fun x => pairSeq (ofNat 0) x)

end DomainTheory.DataTypesAsLattices
