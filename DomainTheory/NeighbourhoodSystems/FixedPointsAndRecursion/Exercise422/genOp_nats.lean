/-ai
The carved-out set is a fixed point of the generating operator.

Apply the least-fixed-point law to the monotone generating operator.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.genOp_monotone

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)



theorem genOp_nats : genOp zero succ (nats zero succ) = nats zero succ :=
  lfpSet_isFixed (genOp zero succ) (genOp_monotone zero succ)

end DomainTheory.NeighbourhoodSystems.Exercise422
