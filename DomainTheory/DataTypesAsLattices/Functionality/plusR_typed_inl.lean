
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plusR_typed_inl {a b x : Pomega} (hx : typed x a) :
    typed (pairSeq (ofNat 0) x) (plusR a b) := by
  rw [typed, plusR_app, pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_zero,
    ← hx]

end DomainTheory.DataTypesAsLattices
