module

public import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_map_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
public import DomainTheory.DataTypesAsLattices.Retracts.plusR

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


namespace plusR_app

theorem app (a b u : Pomega) :
    funOf (plusR a b) u =
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))) :=
  beta (plusR_map_isScottContinuous a b) u

theorem bot (a b : Pomega) :
    funOf (plusR a b) botElem = botElem := by
  rw [plusR_app.app, funOf.bot, dcondSet.bot]

theorem top (a b : Pomega) :
    funOf (plusR a b) topElem = topElem := by
  rw [plusR_app.app, funOf_top, dcondSet.top]

end plusR_app

end DomainTheory.DataTypesAsLattices
