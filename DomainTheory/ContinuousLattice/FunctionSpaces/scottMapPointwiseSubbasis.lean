module

public import DomainTheory.ContinuousLattice.FunctionSpaces.ScottMap
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y]

variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']

variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

def scottMapPointwiseSubbasis (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :
    Set (Set (ScottMap D D')) :=
  { W | ∃ (x : D) (U : Set D'),
      @IsOpen D' scottTopologicalSpace U ∧ W = {f : ScottMap D D' | (f : D → D') x ∈ U} }

end DomainTheory.ContinuousLattice
