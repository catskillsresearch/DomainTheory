/-ai
On a continuous lattice, meet on the right with a fixed element is Scott-continuous.

Continuity follows from preservation of directed suprema by that meet.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.ScottMaps.Basic
public import DomainTheory.ContinuousLattice.ScottMaps.continuous_of_preservesDirectedSup
public import DomainTheory.ContinuousLattice.ScottMaps.meet_preservesDirectedSup

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


theorem proposition_2_7_inf_right (hD : IsContinuousLattice D) (x : D) :
    @Continuous D D scottTopologicalSpace scottTopologicalSpace (fun y => x ⊓ y) :=
  continuous_of_preservesDirectedSup (meet_preservesDirectedSup x hD)

end DomainTheory.ContinuousLattice
