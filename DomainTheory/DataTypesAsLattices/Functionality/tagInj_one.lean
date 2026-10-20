module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem tagInj_one (i : ℕ) (x : Pomega) :
    funOf (tagInj i x) (ofNat 1) = x :=
  pairSeq_app_one (ofNat i) x

end DomainTheory.DataTypesAsLattices
