module

public import DomainTheory.ContinuousLattice.FunctionSpaces.scottMapInducedPiTopology
import DomainTheory.ContinuousLattice.FunctionSpaces.stepMap

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {D D' : Type*} [CompleteLattice D] [CompleteLattice D']

theorem theorem_3_3 (hD : ContinuousLattice D) (hD' : ContinuousLattice D') :
    ContinuousLattice (ScottMap D D') ∧
      (scottTopologicalSpace : TopologicalSpace (ScottMap D D')) =
        scottMapInducedPiTopology.pointwiseTopology D D' :=
  ⟨stepMap.isContinuousLattice hD hD', scottMapInducedPiTopology.scottTopology_eq_pointwise hD hD'⟩

end DomainTheory.ContinuousLattice
