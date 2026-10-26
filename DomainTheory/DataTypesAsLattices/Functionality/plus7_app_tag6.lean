
module

public import DomainTheory.DataTypesAsLattices.Retracts.tagInj
public import DomainTheory.DataTypesAsLattices.Retracts.plus7Body
public import DomainTheory.DataTypesAsLattices.Retracts.plus7
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_ofNat
public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_app
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_zero
public import DomainTheory.DataTypesAsLattices.Functionality.tagInj_one
public import DomainTheory.DataTypesAsLattices.Lambda.dcondSet_more
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem plus7_app_tag6 (a0 a1 a2 a3 a4 a5 a6 x : Pomega) :
    funOf (plus7 a0 a1 a2 a3 a4 a5 a6) (tagInj 6 x) = tagInj 6 (funOf a6 x) := by
  rw [plus7_app, plus7Body, tagInj_zero, tagInj_one, dcondSet.ofNat_succ,
    predSet.ofNat_succ, dcondSet.ofNat_succ, predSet.ofNat_succ,
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 3) (i := 3),
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 4) (i := 2),
    dcondSet.ofNat_succ, predSet_iterate_ofNat (k := 5) (i := 1),
    dcondSet.ofNat_one, predSet_iterate_self, dcondSet.ofNat_zero]

end DomainTheory.DataTypesAsLattices
