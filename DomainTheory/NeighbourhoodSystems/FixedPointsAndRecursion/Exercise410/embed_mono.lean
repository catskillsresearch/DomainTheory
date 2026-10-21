/-ai
If one filter of the relativized system below a lies below another, then the embedding of the first lies below the embedding of the second.

The same witness serves for a neighbourhood of the first embedding, because the neighbourhood of a that belongs to the smaller filter belongs to the larger filter.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

theorem embed_mono (a : V.Element) {g₁ g₂ : (relSystem a).Element} (h : g₁ ≤ g₂) :
    embed a g₁ ≤ embed a g₂ := by
  rintro X ⟨hVX, W, haW, hgW, hWX⟩
  exact ⟨hVX, W, haW, h _ hgW, hWX⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
