/-ai
The seven-tag syntax functor is Scott-continuous.

The seven-fold sum preserves Scott continuity on the constant integer retract, the constant bottom, two identity maps, the diagonal of the four-fold tensor, the diagonal of the binary tensor, and the right continuity of the tensor with the integer retract.
ai-/
module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_diag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.tensor4_diag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.plus7_comp_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem expF_isScottContinuous : IsScottContinuous expF :=
  plus7_comp_isScottContinuous
    (const_isScottContinuous intR)
    (const_isScottContinuous botElem)
    id_isScottContinuous
    id_isScottContinuous
    tensor4_diag_isScottContinuous
    tensorR_diag_isScottContinuous
    (tensorR_right_isScottContinuous intR)

end DomainTheory.DataTypesAsLattices
