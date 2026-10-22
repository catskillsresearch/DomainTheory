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

theorem embed_mono (a : V.Element) {g₁ g₂ : (relSystem a).Element} (h : g₁ ≤ g₂) :
    embed a g₁ ≤ embed a g₂ := by
  rintro X ⟨hVX, W, haW, hgW, hWX⟩
  exact ⟨hVX, W, haW, h _ hgW, hWX⟩

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
