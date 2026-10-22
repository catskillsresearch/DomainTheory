module

public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace IsContinuousLatticeRetraction

/-- **Scott 1972, Prop 2.10 / March 1972 correction (p. 135).** For `S ⊆ D` a subspace of
ambient `D'`, write `⊔S′` for the supremum of `S` computed in `D'` (Scott's prime is on the
index, not the join). This is `sSup (i '' S)` in Lean. -/
noncomputable def ambientSSup (R : IsContinuousLatticeRetraction D D') (S : Set D) : D' :=
  sSup (Set.image (R.incl : D → D') S)

end IsContinuousLatticeRetraction

end DomainTheory.ContinuousLattice
