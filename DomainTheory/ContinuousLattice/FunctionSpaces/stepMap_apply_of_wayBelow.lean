module
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap
public import DomainTheory.ContinuousLattice.FunctionSpaces.stepFun_of_wayBelow
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

theorem stepMap_apply_of_wayBelow {e : D} {e' : D'} {x : D} (h : e ≪ x) :
    (stepMap e e' : D → D') x = e' :=
  stepFun_of_wayBelow h

end DomainTheory.ContinuousLattice
