module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.FunctionSpaces.Projection
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {D : Type*} [CompleteLattice D]

theorem proposition_3_13 (_hD : ContinuousLattice D) :
    Nonempty (ContinuousLatticeProjection D (ScottMap D D)) :=
  ⟨ScottMap.conMinContinuousLatticeProjection⟩

end DomainTheory.ContinuousLattice
