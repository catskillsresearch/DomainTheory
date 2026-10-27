module

public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.graph
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def inleftC : Pomega := graph (fun x => pairSeq (ofNat 0) x)

namespace inleftC

theorem app (x : Pomega) :
    funOf inleftC x = pairSeq (ofNat 0) x :=
  beta (pairSeq_isScottContinuous_right (ofNat 0)) x

end inleftC

end DomainTheory.DataTypesAsLattices
