module

public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup
import DomainTheory.ContinuousLattice.ScottMaps.continuous_preservesDirectedSup

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem proposition_2_5 (f : D → D') :
    (@Continuous D D' scottTopologicalSpace scottTopologicalSpace f) ↔
      PreservesDirectedSup f :=
  ⟨continuous_preservesDirectedSup, fun hf => PreservesDirectedSup.continuous_of hf⟩

end DomainTheory.ContinuousLattice
