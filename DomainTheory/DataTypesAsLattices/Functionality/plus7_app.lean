module

public import DomainTheory.DataTypesAsLattices.Functionality.funOf_top
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_map_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Graph.funOf_more
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.plus7
public import DomainTheory.DataTypesAsLattices.Retracts.plus7Body
public import DomainTheory.DataTypesAsLattices.Retracts.tagInj

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace plus7_app

theorem app (a0 a1 a2 a3 a4 a5 a6 u : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) u =
      plus7Body a0 a1 a2 a3 a4 a5 a6 u :=
  beta (plus7_map_isScottContinuous a0 a1 a2 a3 a4 a5 a6) u

theorem bot (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) botElem = botElem := by
  rw [plus7_app.app, plus7Body, funOf.bot, dcondSet.bot]

theorem top (a0 a1 a2 a3 a4 a5 a6 : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) topElem = topElem := by
  rw [plus7_app.app, plus7Body, funOf_top, dcondSet.top]

theorem tag0 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 0 x) = tagInj 0 (funOf a0 x) := by
  rw [plus7_app.app, plus7Body, tagInj_zero, tagInj_one, dcondSet.ofNat_zero]

theorem tag1 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 1 x) = tagInj 1 (funOf a1 x) := by
  rw [plus7_app.app, plus7Body, tagInj_zero, tagInj_one, predSet.ofNat_succ,
    dcondSet.ofNat_one, dcondSet.ofNat_zero]

theorem tag2 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 2 x) = tagInj 2 (funOf a2 x) := by
  rw [plus7_app.app, plus7Body, tagInj_zero, tagInj_one, predSet.ofNat_succ,
    dcondSet.ofNat_succ, predSet.ofNat_succ, dcondSet.ofNat_one,
    dcondSet.ofNat_zero]

theorem tag3 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 3 x) = tagInj 3 (funOf a3 x) := by
  rw [plus7_app.app, plus7Body, tagInj_zero, tagInj_one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_one, predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag4 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 4 x) = tagInj 4 (funOf a4 x) := by
  rw [plus7_app.app, plus7Body, tagInj_zero, tagInj_one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 1),
    dcondSet.ofNat_one, predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag5 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 5 x) = tagInj 5 (funOf a5 x) := by
  rw [plus7_app.app, plus7Body, tagInj_zero, tagInj_one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 2),
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 1),
    dcondSet.ofNat_one, predSet_iterate_self, dcondSet.ofNat_zero]

theorem tag6 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 6 x) = tagInj 6 (funOf a6 x) := by
  rw [plus7_app.app, plus7Body, tagInj_zero, tagInj_one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 2),
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 5) (i := 1),
    dcondSet.ofNat_one, predSet_iterate_self, dcondSet.ofNat_zero]

end plus7_app

end DomainTheory.DataTypesAsLattices
