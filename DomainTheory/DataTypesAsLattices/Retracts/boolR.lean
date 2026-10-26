module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Graph.beta

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- **Scott 1976, (4.3).** Boolean retract via the doubly strict conditional. -/
def boolR : Pomega :=
  graph (fun u => dcondSet u (ofNat 0) (ofNat 1))

namespace boolR

theorem app (u : Pomega) :
    funOf boolR u = dcondSet u (ofNat 0) (ofNat 1) :=
  beta (dcondSet_isScottContinuous_left (ofNat 0) (ofNat 1)) u

end boolR

end DomainTheory.DataTypesAsLattices
