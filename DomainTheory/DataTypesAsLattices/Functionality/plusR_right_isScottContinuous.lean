/-ai
For a fixed retract parameter a, the map sending b to a ⊕ b is Scott continuous.

Continuity of the graph in the parameter b reduces to continuity of the body at each fixed u. Theorem 1.3 composes right continuity of the double conditional, at the fixed tag application and the fixed left branch, with the composite of right continuity of sequence pairing at the numeral 1 and left continuity of application at the first component of u.
ai-/

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
