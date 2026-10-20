module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices



theorem pairSeq_app_one (x y : Pomega) : funOf (pairSeq x y) (ofNat 1) = y :=
  seq2_app_one x y

end DomainTheory.DataTypesAsLattices
