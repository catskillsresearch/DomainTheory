
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_dcondSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plusR_snd (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 1) =
      dcondSet (funOf u (ofNat 0))
        (funOf a (funOf u (ofNat 1))) (funOf b (funOf u (ofNat 1))) := by
  rw [plusR_app, funOf_dcondSet, pairSeq_app_one, pairSeq_app_one]

end DomainTheory.DataTypesAsLattices
