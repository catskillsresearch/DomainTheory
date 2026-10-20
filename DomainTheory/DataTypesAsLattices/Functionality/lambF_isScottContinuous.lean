module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.arrowR_diag_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices
































theorem lambF_isScottContinuous : IsScottContinuous lambF :=
  theorem_1_3 (f := fun b => plusR intR b) (g := fun z => arrowR z z)
    (plusR_right_isScottContinuous intR)
    arrowR_diag_isScottContinuous

end DomainTheory.DataTypesAsLattices
