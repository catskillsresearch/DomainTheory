
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tensorR_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => tensorR a b) :=
  graph_const_isScottContinuous
    (fun b u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1))))
    (fun u =>
      theorem_1_3
        (f := fun y => pairSeq (funOf a (funOf u (ofNat 0))) y)
        (g := fun b => funOf b (funOf u (ofNat 1)))
        (pairSeq_isScottContinuous_right (funOf a (funOf u (ofNat 0))))
        (funOf_isScottContinuous_left (funOf u (ofNat 1))))

end DomainTheory.DataTypesAsLattices
