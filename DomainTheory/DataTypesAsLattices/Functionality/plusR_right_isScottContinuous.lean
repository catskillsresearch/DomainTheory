module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices






























theorem plusR_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun b => plusR a b) :=
  graph_const_isScottContinuous
    (fun b u =>
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1)))))
    (fun u =>
      theorem_1_3
        (f := fun y =>
          dcondSet (funOf u (ofNat 0))
            (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1)))) y)
        (g := fun b => pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1))))
        (dcondSet_isScottContinuous_right
          (funOf u (ofNat 0))
          (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1)))))
        (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 1))
          (funOf_isScottContinuous_left (funOf u (ofNat 1)))))

end DomainTheory.DataTypesAsLattices
