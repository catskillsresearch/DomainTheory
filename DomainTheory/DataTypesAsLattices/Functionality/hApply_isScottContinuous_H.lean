module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem hApply_isScottContinuous_H (e t : Pomega) :
    IsScottContinuous (fun H => hApply H e t) :=
  theorem_1_3 (f := fun u => funOf u t) (g := fun H => funOf H e)
    (funOf_isScottContinuous_left t) (funOf_isScottContinuous_left e)

end DomainTheory.DataTypesAsLattices
