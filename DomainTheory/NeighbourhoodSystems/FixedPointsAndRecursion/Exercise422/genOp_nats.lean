module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.genOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.subZero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.subSucc
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.peanoSub
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.natPeano
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.zero_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.succ_mem_nats
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats_induction
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.Nat'
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.genOp_monotone

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_isFixed
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)


theorem genOp_nats : genOp zero succ (nats zero succ) = nats zero succ :=
  lfpSet_isFixed (genOp zero succ) (genOp_monotone zero succ)

end DomainTheory.NeighbourhoodSystems.Exercise422
