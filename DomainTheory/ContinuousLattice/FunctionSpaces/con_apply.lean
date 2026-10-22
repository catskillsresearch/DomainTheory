module

public import DomainTheory.ContinuousLattice.FunctionSpaces.con_
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace Proposition313

@[simp] theorem con_apply (x y : D) : ((con x : ScottMap D D) : D → D) y = x := rfl

end Proposition313

end DomainTheory.ContinuousLattice
