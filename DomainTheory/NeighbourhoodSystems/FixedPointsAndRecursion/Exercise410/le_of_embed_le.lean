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

theorem le_of_embed_le (a : V.Element) {g₁ g₂ : (relSystem a).Element}
    (h : embed a g₁ ≤ embed a g₂) : g₁ ≤ g₂ := by
  intro X hg₁X
  have hVX : V.mem X := a.sub (g₁.sub hg₁X)
  have : (embed a g₂).mem X := h X ⟨hVX, X, g₁.sub hg₁X, hg₁X, subset_rfl⟩
  obtain ⟨_, W, haW, hg₂W, hWX⟩ := this
  exact g₂.up_mem hg₂W (g₁.sub hg₁X) hWX

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
