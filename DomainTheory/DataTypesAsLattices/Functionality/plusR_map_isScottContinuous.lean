module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices















theorem plusR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet (funOf u (ofNat 0))
        (pairSeq (ofNat 0) (funOf a (funOf u (ofNat 1))))
        (pairSeq (ofNat 1) (funOf b (funOf u (ofNat 1))))) :=
  continuous_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 0))
      (theorem_1_3 (funOf_isScottContinuous a)
        (funOf_isScottContinuous_left (ofNat 1))))
    (theorem_1_3 (pairSeq_isScottContinuous_right (ofNat 1))
      (theorem_1_3 (funOf_isScottContinuous b)
        (funOf_isScottContinuous_left (ofNat 1))))

end DomainTheory.DataTypesAsLattices
