
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairElem_snd (x y : Pomega) : funOf (pairElem x y) (ofNat 1) = y :=
  seq2_app_one x y

end DomainTheory.DataTypesAsLattices
