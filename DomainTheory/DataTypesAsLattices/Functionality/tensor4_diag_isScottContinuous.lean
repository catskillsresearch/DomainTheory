
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.seq4_comp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem tensor4_diag_isScottContinuous :
    IsScottContinuous (fun z => tensor4 z z z z) :=
  graph_const_isScottContinuous
    (fun z u =>
      seq4 (funOf z (funOf u (ofNat 0)))
        (funOf z (funOf u (ofNat 1)))
        (funOf z (funOf u (ofNat 2)))
        (funOf z (funOf u (ofNat 3))))
    (fun u =>
      seq4_comp_isScottContinuous
        (funOf_isScottContinuous_left (funOf u (ofNat 0)))
        (funOf_isScottContinuous_left (funOf u (ofNat 1)))
        (funOf_isScottContinuous_left (funOf u (ofNat 2)))
        (funOf_isScottContinuous_left (funOf u (ofNat 3))))

end DomainTheory.DataTypesAsLattices
