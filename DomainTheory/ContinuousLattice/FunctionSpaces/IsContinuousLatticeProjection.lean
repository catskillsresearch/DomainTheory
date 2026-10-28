module

public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

universe u v

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

structure IsContinuousLatticeProjection (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D']
    extends IsContinuousLatticeRetraction D D' where
  incl_retr_le : ∀ d,
    @LE.le D'
      (ChainCompletePartialOrder.instOfCompleteLattice (α := D')).toPartialOrder.toPreorder.toLE
      (incl (retr d)) d

end DomainTheory.ContinuousLattice
