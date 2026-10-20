module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


































































theorem boolR_app (u : Pomega) :
    funOf boolR u = dcondSet u (ofNat 0) (ofNat 1) :=
  beta (dcondSet_isScottContinuous_left (ofNat 0) (ofNat 1)) u

end DomainTheory.DataTypesAsLattices
