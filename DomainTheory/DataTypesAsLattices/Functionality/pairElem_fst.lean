module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem pairElem_fst (x y : Pomega) : funOf (pairElem x y) (ofNat 0) = x :=
  seq2_app_zero x y

end DomainTheory.DataTypesAsLattices
