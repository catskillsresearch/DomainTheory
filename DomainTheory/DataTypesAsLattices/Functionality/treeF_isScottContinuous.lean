
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_diag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_right_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem treeF_isScottContinuous : IsScottContinuous treeF :=
  theorem_1_3 (f := fun b => plusR botElem b) (g := fun z => tensorR z z)
    (plusR_right_isScottContinuous botElem)
    tensorR_diag_isScottContinuous

end DomainTheory.DataTypesAsLattices
