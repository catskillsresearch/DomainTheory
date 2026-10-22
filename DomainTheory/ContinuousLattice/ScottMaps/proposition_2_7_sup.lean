/-ai
Binary join, as a map on the product of a complete lattice with itself, is Scott-continuous. This is the join clause of Scott's Proposition 2.7, and it holds on every complete lattice.

Continuity follows from preservation of directed suprema. That preservation is the directed-supremum identity for Scott-continuous binary join.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.ScottMaps.Basic
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


/-- **Scott 1972, Proposition 2.7 (join).** Binary join is Scott-continuous on every complete
lattice; this is the `⊔`-part of Scott's 2.7. -/
theorem proposition_2_7_sup :
    @Continuous (D × D) D scottTopologicalSpace scottTopologicalSpace (fun p : D × D => p.1 ⊔ p.2) :=
  continuous_of_preservesDirectedSup <| by
    intro S hS hSdir
    simpa using (ScottContinuous.sup₂ (β := D) (d := S) hS hSdir (isLUB_sSup S)).sSup_eq.symm

end DomainTheory.ContinuousLattice
