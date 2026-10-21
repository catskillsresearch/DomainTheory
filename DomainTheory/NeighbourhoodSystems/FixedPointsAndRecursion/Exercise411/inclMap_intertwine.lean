/-ai
The inclusion of the relativized system intertwines the restriction of an endomap f with f: the inclusion of the image of a filter under the restriction equals the image under f of the inclusion of that filter.

Both sides are rewritten by the elementwise action of the inclusion, and the action of the restriction under the embedding gives the equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise407
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise411.inclMap_toElementMap

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relMap_toElementMap_embed
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- The inclusion intertwines `f'` with `f`: `ι ∘ f' = f ∘ ι` (from `relMap_toElementMap_embed`). -/
theorem inclMap_intertwine (f : ApproximableMap V V) {a : V.Element} (ha : f.toElementMap a = a)
    (g : (relSystem a).Element) :
    (inclMap a).toElementMap ((relMap f ha).toElementMap g) =
      f.toElementMap ((inclMap a).toElementMap g) := by
  rw [inclMap_toElementMap, inclMap_toElementMap, relMap_toElementMap_embed]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
