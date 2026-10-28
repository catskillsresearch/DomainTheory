module

public import DomainTheory.ContinuousLattice.FunctionSpaces.const
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

@[simp] theorem const_apply (c : D') (x : D) : (ScottMap.const c : D → D') x = c := rfl

end ScottMap

end DomainTheory.ContinuousLattice
