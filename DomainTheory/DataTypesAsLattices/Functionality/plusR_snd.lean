
module

public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
public import DomainTheory.DataTypesAsLattices.Functionality.funOf_dcondSet

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plusR_snd (a b u : Pomega) :
    funOf (funOf (plusR a b) u) (ofNat 1) =
      dcondSet (funOf u (ofNat 0))
        (funOf a (funOf u (ofNat 1))) (funOf b (funOf u (ofNat 1))) := by
  rw [plusR_app.app, funOf_dcondSet, pairSeq_app_one, pairSeq_app_one]

end DomainTheory.DataTypesAsLattices
