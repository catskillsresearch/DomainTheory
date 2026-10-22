module

public import DomainTheory.ContinuousLattice.Specialization.scottTopologicalSpace
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

/-- **March 1972 correction.** The given topology `τ` is coarser than (or equal to) the Scott
topology: every set open in `τ` is Scott-open. Equivalently `Opens(τ) ⊆ Opens(Scott)`,
i.e. `scottTopologicalSpace ≤ τ` in mathlib's order on topologies. -/
def CoarserThanScottTopology (τ : TopologicalSpace D) : Prop :=
  scottTopologicalSpace ≤ τ

end DomainTheory.ContinuousLattice
