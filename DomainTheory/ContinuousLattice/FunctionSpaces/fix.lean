module

public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.toOrderHom
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace Proposition314

noncomputable def fix (f : ScottMap D D) : D := (toOrderHom f).lfp

end Proposition314

end DomainTheory.ContinuousLattice
