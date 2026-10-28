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

theorem fix_le {f : ScottMap D D} {x : D} (h : (f : D → D) x ≤ x) : fix f ≤ x :=
  (toOrderHom f).lfp_le h

end Proposition314

end DomainTheory.ContinuousLattice
