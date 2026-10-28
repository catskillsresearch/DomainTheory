module

public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import DomainTheory.DataTypesAsLattices.Retracts.expF
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.Lambda.id_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.const_isScottContinuous
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
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
