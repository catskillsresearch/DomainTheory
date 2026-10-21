/-ai
The generating operator is monotone.

The zero clause is unchanged. A successor witness in the smaller set is a successor witness in the larger set by the assumed inclusion.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.Basic

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
