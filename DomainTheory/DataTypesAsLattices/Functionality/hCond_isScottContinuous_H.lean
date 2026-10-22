module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.continuous_nary
public import DomainTheory.DataTypesAsLattices.Functionality.hApply_isScottContinuous_H

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hCond_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hCond H e t) :=
  theorem_1_3 (funOf_isScottContinuous lambR)
    (continuous_nary
      (fun y z => condSet_isScottContinuous_left y z)
      (fun x z => condSet_isScottContinuous_mid x z)
      (fun x y => condSet_isScottContinuous_right x y)
      (theorem_1_3 (funOf_isScottContinuous whichC)
        (hApply_isScottContinuous_H _ t))
      (continuous_nary
        (fun y z => condSet_isScottContinuous_left y z)
        (fun x z => condSet_isScottContinuous_mid x z)
        (fun x y => condSet_isScottContinuous_right x y)
        (theorem_1_3 (funOf_isScottContinuous outC)
          (hApply_isScottContinuous_H _ t))
        (hApply_isScottContinuous_H _ t)
        (hApply_isScottContinuous_H _ t))
      (hApply_isScottContinuous_H _ t))

end DomainTheory.DataTypesAsLattices
