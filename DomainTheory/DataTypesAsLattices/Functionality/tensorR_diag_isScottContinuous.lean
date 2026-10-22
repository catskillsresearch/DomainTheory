
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tensorR_diag_isScottContinuous :
    IsScottContinuous (fun z => tensorR z z) :=
  graph_const_isScottContinuous
    (fun z u =>
      pairSeq (funOf z (funOf u (ofNat 0))) (funOf z (funOf u (ofNat 1))))
    (fun u =>
      continuous_tuple
        (fun y => pairSeq_isScottContinuous_left y)
        (fun x => pairSeq_isScottContinuous_right x)
        (funOf_isScottContinuous_left (funOf u (ofNat 0)))
        (funOf_isScottContinuous_left (funOf u (ofNat 1))))

end DomainTheory.DataTypesAsLattices
