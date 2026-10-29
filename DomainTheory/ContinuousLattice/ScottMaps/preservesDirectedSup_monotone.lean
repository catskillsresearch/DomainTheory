module

public import DomainTheory.ContinuousLattice.ScottMaps.PreservesDirectedSup

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set

variable {D D' D'' : Type*} [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

theorem preservesDirectedSup_monotone {f : D → D'} (hf : PreservesDirectedSup f) :
    Monotone f :=
  PreservesDirectedSup.monotone hf

end DomainTheory.ContinuousLattice
