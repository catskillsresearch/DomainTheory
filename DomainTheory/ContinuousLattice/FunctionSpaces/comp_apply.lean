module

public import DomainTheory.ContinuousLattice.FunctionSpaces.comp
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

@[simp] theorem comp_apply (f : ScottMap D' D'') (g : ScottMap D D') (x : D) :
    (f.comp g : D → D'') x = f (g x) := rfl

end ScottMap

end DomainTheory.ContinuousLattice
