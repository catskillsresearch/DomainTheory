module

public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.tensorR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def treeF (z : Pomega) : Pomega := plusR botElem (tensorR z z)

namespace treeF

theorem isScottContinuous : IsScottContinuous treeF :=
  theorem_1_3 (f := fun b => plusR botElem b) (g := fun z => tensorR z z)
    (plusR.right_isScottContinuous botElem)
    tensorR.diag_isScottContinuous

end treeF

end DomainTheory.DataTypesAsLattices
