module

public import DomainTheory.ContinuousLattice.FunctionSpaces.le_refl'
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_trans'
public import DomainTheory.ContinuousLattice.FunctionSpaces.le_antisymm'
public import DomainTheory.ContinuousLattice.FunctionSpaces.lt_iff_le_not_ge'
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

instance instPartialOrder {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : PartialOrder (ScottMap D D') where
  le := ScottMap.le
  lt := ScottMap.lt
  le_refl := le_refl'
  le_trans := le_trans'
  lt_iff_le_not_ge := lt_iff_le_not_ge'
  le_antisymm := le_antisymm'

end ScottMap

end DomainTheory.ContinuousLattice
