
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem inrightC_app (x : Pomega) :
    funOf inrightC x = pairSeq (ofNat 1) x :=
  beta (pairSeq_isScottContinuous_right (ofNat 1)) x

end DomainTheory.DataTypesAsLattices
