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

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)


/-- **Exercise 4.22 (Scott 1981, PRG-19).** *Yes:* whenever `N*` satisfies (i) and (ii), there is a
subset `N ⊆ N*` (carrying the inherited structure) satisfying (i), (ii), and (iii). -/
theorem exists_peano_submodel (hzero : ∀ n, zero ≠ succ n) (hinj : Function.Injective succ) :
    Nonempty (PeanoModel (Nat' zero succ)) :=
  ⟨peanoSub zero succ hzero hinj⟩

end DomainTheory.NeighbourhoodSystems.Exercise422
