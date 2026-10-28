module

public import DomainTheory.ContinuousLattice.FunctionSpaces.fix
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

theorem fix_eq (f : ScottMap D D) : (f : D → D) (fix f) = fix f :=
  (toOrderHom f).map_lfp

end Proposition314

end DomainTheory.ContinuousLattice
