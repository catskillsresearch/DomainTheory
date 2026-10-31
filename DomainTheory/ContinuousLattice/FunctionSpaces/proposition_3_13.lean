module

import DomainTheory.ContinuousLattice.FunctionSpaces.Projection
public import DomainTheory.ContinuousLattice.FunctionSpaces.ContinuousLatticeProjection

@[expose] public section

namespace DomainTheory.ContinuousLattice

variable {D : Type*} [CompleteLattice D]

theorem proposition_3_13 (_hD : ContinuousLattice D) :
    Nonempty (ContinuousLatticeProjection D (ScottMap D D)) :=
  ⟨ScottMap.conMinContinuousLatticeProjection⟩

end DomainTheory.ContinuousLattice
