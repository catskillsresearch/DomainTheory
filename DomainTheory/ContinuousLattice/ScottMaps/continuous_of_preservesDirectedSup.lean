module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
import all Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
import all Mathlib.Topology.Order.ScottTopology
public import DomainTheory.ContinuousLattice.ScottMaps.Basic
public import DomainTheory.ContinuousLattice.ScottMaps.scottOpen_preimage

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']


theorem continuous_of_preservesDirectedSup {f : D → D'} (hf : PreservesDirectedSup f) :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace f := by
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff_scottOpen] at hU ⊢
  exact scottOpen_preimage hf hU

end DomainTheory.ContinuousLattice
