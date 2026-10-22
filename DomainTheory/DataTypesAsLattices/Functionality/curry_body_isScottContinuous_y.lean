module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem curry_body_isScottContinuous_y (u x : Pomega) :
    IsScottContinuous (fun y => funOf u (pairSeq x y)) :=
  theorem_1_3 (funOf_isScottContinuous u) (pairSeq_isScottContinuous_right x)

end DomainTheory.DataTypesAsLattices
