
module

public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.treeF
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
public import DomainTheory.DataTypesAsLattices.Pomega.e
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_diag_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_right_isScottContinuous

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem treeF_isScottContinuous : IsScottContinuous treeF :=
  theorem_1_3 (f := fun b => plusR botElem b) (g := fun z => tensorR z z)
    (plusR_right_isScottContinuous botElem)
    tensorR_diag_isScottContinuous

end DomainTheory.DataTypesAsLattices
