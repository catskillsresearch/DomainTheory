/-ai
Any fixed point of an approximable endomap f that lies below the least fixed point of f equals that least fixed point.

A fixed point satisfies the pre-fixed-point inequality, so minimality of the least fixed point places it below the given fixed point, and the two inequalities give equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
















/-- **Exercise 4.10 (Scott 1981, PRG-19).** Any fixed point of `f` below `fix(f)` *is* `fix(f)`:
a fixed point is a pre-fixed point, so leastness forces `fix(f) ⊑ x`. -/
theorem fixElement_below_unique (f : ApproximableMap V V) {x : V.Element}
    (hxle : x ≤ f.fixElement) (hxfix : f.toElementMap x = x) : x = f.fixElement := by
  have hge : f.fixElement ≤ x := fixElement_le_of_toElementMap_le f (le_of_eq hxfix)
  exact le_antisymm hxle hge

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
