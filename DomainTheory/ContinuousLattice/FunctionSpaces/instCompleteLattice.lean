module

public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic.isLUB_sSup
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

section Projections

namespace Projections

/-- **Scott 1972, Proposition 3.12.** `J_D` is a complete lattice (a `⊔`-closed subspace of
`[D → D]`). Suprema are inherited from `[D → D]`; infima are derived by `completeLatticeOfSup`. -/
noncomputable instance instCompleteLattice : CompleteLattice (Projections D) :=
  completeLatticeOfSup (Projections D) isLUB_sSup

end Projections

end Projections

end DomainTheory.ContinuousLattice
