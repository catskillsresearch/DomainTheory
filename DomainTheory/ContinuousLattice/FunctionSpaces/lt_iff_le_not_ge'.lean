module

public import DomainTheory.ContinuousLattice.FunctionSpaces.lt
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

universe u v

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace ScottMap

theorem lt_iff_le_not_ge' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D') :
    ScottMap.lt f g ↔
      ScottMap.le f g ∧ ¬ ScottMap.le g f :=
  Iff.rfl

end ScottMap

end DomainTheory.ContinuousLattice
