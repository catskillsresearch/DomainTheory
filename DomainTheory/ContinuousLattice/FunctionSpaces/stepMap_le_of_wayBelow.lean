module
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap_apply_of_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_not_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_def
public import DomainTheory.ContinuousLattice.FunctionSpaces.BasicInst28
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

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
