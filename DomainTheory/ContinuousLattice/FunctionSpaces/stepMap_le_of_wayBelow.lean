module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
import all Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
import all Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
import all Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
import all Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
import all Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_apply_of_wayBelow

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']




















/-- If `e' ≪ g e` then the step function `ē[e, e']` lies below `g` (a pointwise argument). -/
theorem stepMap_le_of_wayBelow {e : D} {e' : D'} {g : ScottMap D D'}
    (h : e' ≪ (g : D → D') e) : stepMap e e' ≤ g := by
  rw [ScottMap.le_def]
  intro x
  by_cases hex : e ≪ x
  · rw [stepMap_apply_of_wayBelow hex]
    exact h.le.trans (g.monotone hex.le)
  · show stepFun e e' x ≤ (g : D → D') x
    rw [stepFun_of_not_wayBelow hex]
    exact bot_le

end DomainTheory.ContinuousLattice
