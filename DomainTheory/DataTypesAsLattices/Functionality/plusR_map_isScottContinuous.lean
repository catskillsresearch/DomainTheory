/-ai
The map sending u to the double conditional of the application of u at the numeral 0, with left branch the sequence pair of the numeral 0 and the application of a to the application of u at the numeral 1, and right branch the sequence pair of the numeral 1 and the application of b to that same application, is Scott continuous.

The continuity theorem for an operation of three arguments is applied to the three continuity lemmas for the double conditional, to left continuity of application at the numeral 0, and to the two branches. Each branch is Theorem 1.3 applied to right continuity of sequence pairing at a constant tag and to the composite of application of a, or of b, with left application at the numeral 1.
ai-/

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
