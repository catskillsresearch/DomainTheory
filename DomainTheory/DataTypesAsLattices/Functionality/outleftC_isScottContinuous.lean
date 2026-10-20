module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_tuple

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















theorem outleftC_isScottContinuous :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0)) (funOf u (ofNat 1)) botElem) :=
  continuous_tuple
    (fun y => condSet_isScottContinuous_left y botElem)
    (fun tes => condSet_isScottContinuous_mid tes botElem)
    (funOf_isScottContinuous_left (ofNat 0))
    (funOf_isScottContinuous_left (ofNat 1))

end DomainTheory.DataTypesAsLattices
