/-ai
The elementwise action of the inclusion of the relativized system below an element a is the embedding of the relativized filter.

Extensionality compares membership. A witness that a neighbourhood belongs to the image under the inclusion is a neighbourhood of the filter, belonging to a and contained in the target, which is a witness for the embedding, and conversely.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap




/-- The inclusion's elementwise action is `embed a` (Exercise 4.10). -/
theorem inclMap_toElementMap (a : V.Element) (g : (relSystem a).Element) :
    (inclMap a).toElementMap g = embed a g := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hgX, haX, hVY, hXY⟩
    exact ⟨hVY, X, haX, hgX, hXY⟩
  · rintro ⟨hVY, W, haW, hgW, hWY⟩
    exact ⟨W, hgW, haW, hVY, hWY⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
