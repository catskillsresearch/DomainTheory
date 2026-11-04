module

public import DomainTheory.DataTypesAsLattices.Retracts.pairSeq
import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace PairSeq

theorem app_zero (x y : Pomega) : funOf (pairSeq x y) (ofNat 0) = x :=
  seq2.zero x y

theorem app_one (x y : Pomega) : funOf (pairSeq x y) (ofNat 1) = y :=
  seq2.one x y

theorem inj {x y x' y' : Pomega} (h : pairSeq x y = pairSeq x' y') :
    x = x' ∧ y = y' := by
  constructor
  · have := congrArg (fun w => funOf w (ofNat 0)) h
    rw [app_zero, app_zero] at this
    exact this
  · have := congrArg (fun w => funOf w (ofNat 1)) h
    rw [app_one, app_one] at this
    exact this

theorem isScottContinuous_left (y : Pomega) :
    IsScottContinuous (fun x => pairSeq x y) :=
  graph_const_isScottContinuous
    (fun x z => condSet z x (condSet (predSet z) y botElem))
    (fun z => condSet.isScottContinuous_mid z _)

theorem isScottContinuous_right (x : Pomega) :
    IsScottContinuous (fun y => pairSeq x y) :=
  graph_const_isScottContinuous
    (fun y z => condSet z x (condSet (predSet z) y botElem))
    (fun z =>
      theorem_1_3 (condSet.isScottContinuous_right z x)
        (condSet.isScottContinuous_mid (predSet z) botElem))

end PairSeq

end DomainTheory.DataTypesAsLattices
