
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tensorR_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      pairSeq (funOf a (funOf u (ofNat 0))) (funOf b (funOf u (ofNat 1)))) :=
  continuous_tuple
    (fun y => pairSeq_isScottContinuous_left y)
    (fun x => pairSeq_isScottContinuous_right x)
    (theorem_1_3 (funOf_isScottContinuous a) (funOf_isScottContinuous_left (ofNat 0)))
    (theorem_1_3 (funOf_isScottContinuous b) (funOf_isScottContinuous_left (ofNat 1)))

end DomainTheory.DataTypesAsLattices
