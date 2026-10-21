/-ai
If the embedding of one relativized filter lies below the embedding of another, then the first filter lies below the second.

A neighbourhood of the first filter belongs to a, so it is a neighbourhood of the first embedding and hence of the second. The witness for that membership is a neighbourhood of the second filter contained in the original neighbourhood, and upward closure of the second filter, using that the original neighbourhood belongs to a, returns it to that filter.
ai-/
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
