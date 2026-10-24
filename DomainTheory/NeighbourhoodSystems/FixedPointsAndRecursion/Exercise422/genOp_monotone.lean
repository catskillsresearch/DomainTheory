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


theorem genOp_monotone : Monotone (genOp zero succ) := by
  intro x y hxy z hz
  rcases hz with hz | ⟨a, ha, rfl⟩
  · exact Or.inl hz
  · exact Or.inr ⟨a, hxy ha, rfl⟩

end DomainTheory.NeighbourhoodSystems.Exercise422
