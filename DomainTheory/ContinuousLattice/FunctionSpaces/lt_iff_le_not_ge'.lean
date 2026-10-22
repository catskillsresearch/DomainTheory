/-ai
The strict pointwise order on Scott maps is the pointwise order together with the failure of the reverse inequality.

The equivalence is the definition of the strict order.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMapProjection
public import DomainTheory.ContinuousLattice.FunctionSpaces.le
public import DomainTheory.ContinuousLattice.FunctionSpaces.lt

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

/-- The chosen strict pointwise order is `≤ ∧ ¬ ≥`. -/
theorem lt_iff_le_not_ge' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D') :
    ScottMap.lt f g ↔
      ScottMap.le f g ∧ ¬ ScottMap.le g f :=
  Iff.rfl

end ScottMap

end DomainTheory.ContinuousLattice
