
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem sumMed_body_isScottContinuous (f g : Pomega) :
    IsScottContinuous (fun u =>
      condSet (funOf u (ofNat 0))
        (funOf f (funOf u (ofNat 1)))
        (funOf g (funOf u (ofNat 1)))) :=
  continuous_nary
    (fun y z => condSet_isScottContinuous_left y z)
    (fun x z => condSet_isScottContinuous_mid x z)
    (fun x y => condSet_isScottContinuous_right x y)
    (funOf_isScottContinuous_left (ofNat 0))
    (theorem_1_3 (funOf_isScottContinuous f)
      (funOf_isScottContinuous_left (ofNat 1)))
    (theorem_1_3 (funOf_isScottContinuous g)
      (funOf_isScottContinuous_left (ofNat 1)))

end DomainTheory.DataTypesAsLattices
