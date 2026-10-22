module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- `embed a g ⊑ a`: the embedding lands below `a`. -/
theorem embed_le (a : V.Element) (g : (relSystem a).Element) : embed a g ≤ a := by
  rintro X ⟨hVX, W, haW, _, hWX⟩
  exact a.up_mem haW hVX hWX

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
