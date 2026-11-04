module

public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Retracts.arrowR
public import DomainTheory.DataTypesAsLattices.Retracts.plusR
public import DomainTheory.DataTypesAsLattices.Retracts.intR
public import Mathlib.Order.CompleteLattice.Defs
public import DomainTheory.DataTypesAsLattices.FixedPoint.theorem_1_3
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Order
public import Mathlib.Topology.Separation.Basic
public import DomainTheory.DataTypesAsLattices.Continuous.IsScottContinuous
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def lambF (z : Pomega) : Pomega := plusR intR (arrowR z z)

namespace lambF

theorem isScottContinuous : IsScottContinuous lambF :=
  theorem_1_3 (f := fun b => plusR intR b) (g := fun z => arrowR z z)
    (plusR.right_isScottContinuous intR)
    arrowR.diag_isScottContinuous

end lambF

end DomainTheory.DataTypesAsLattices
