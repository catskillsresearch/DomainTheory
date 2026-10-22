/-ai
A projection of continuous lattices, in the sense of Scott's Definition 3.6, is a retraction of continuous lattices together with the inequality that the inclusion after the retraction lies below the identity.
ai-/
module


public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

/-- **Scott 1972, Definition 3.6.** A *projection* of continuous lattices: a retract with
`i ∘ j ⊑ id`. -/
structure IsContinuousLatticeProjection (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D']
    extends IsContinuousLatticeRetraction D D' where
  incl_retr_le : ∀ d,
    @LE.le D'
      (ChainCompletePartialOrder.instOfCompleteLattice (α := D')).toPartialOrder.toPreorder.toLE
      (incl (retr d)) d

end DomainTheory.ContinuousLattice
