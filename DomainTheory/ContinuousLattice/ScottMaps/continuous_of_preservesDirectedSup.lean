/-ai
A map that preserves directed suprema is continuous for the Scott topologies.

Continuity is tested on opens. An open of the codomain is Scott-open, and its preimage under a map preserving directed suprema is Scott-open, hence open in the Scott topology.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import Mathlib.Order.ScottContinuity
public import Mathlib.Topology.Order.ScottTopology
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
