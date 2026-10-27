module

public import DomainTheory.DataTypesAsLattices.Functionality.predSet_iterate_self
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_body_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Graph.beta
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Lambda.condSet
public import DomainTheory.DataTypesAsLattices.Lambda.ofNat
public import DomainTheory.DataTypesAsLattices.Lambda.predSet
public import DomainTheory.DataTypesAsLattices.Lambda.predSet_more
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Retracts.seq4

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


namespace seq4_app

theorem app (a b c d z : Pomega) :
    funOf (seq4 a b c d) z =
      condSet z a
        (condSet (predSet z) b
          (condSet (predSet (predSet z)) c
            (condSet (predSet^[3] z) d botElem))) :=
  beta (seq4_body_isScottContinuous a b c d) z

theorem zero (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 0) = a := by
  rw [seq4_app.app, condSet.ofNat_zero]

theorem one (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 1) = b := by
  rw [seq4_app.app, condSet.ofNat_one, predSet.ofNat_succ, condSet.ofNat_zero]

theorem two (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 2) = c := by
  rw [seq4_app.app, condSet.ofNat_succ, predSet.ofNat_succ, condSet.ofNat_one,
    predSet.ofNat_succ, condSet.ofNat_zero]

theorem three (a b c d : Pomega) :
    funOf (seq4 a b c d) (ofNat 3) = d := by
  rw [seq4_app.app, condSet.ofNat_succ, predSet.ofNat_succ, condSet.ofNat_succ,
    predSet.ofNat_succ, condSet.ofNat_one, predSet_iterate_self,
    condSet.ofNat_zero]

end seq4_app

end DomainTheory.DataTypesAsLattices
