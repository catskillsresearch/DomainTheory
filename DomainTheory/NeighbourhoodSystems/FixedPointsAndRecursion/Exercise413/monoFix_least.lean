/-ai
The infimum of the pre-fixed points of f is the least fixed point: it lies below every fixed point.

A fixed point satisfies the pre-fixed-point inequality, so the comparison with pre-fixed points applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise413.monoFix_le_preFix

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem





/-- **Exercise 4.13(1) (Scott 1981, PRG-19).** `monoFix f ha` is the *least* fixed point: any `y`
with `f(y) = y` satisfies `b ⊑ y`. -/
theorem monoFix_least (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a)
    {y : V.Element} (hy : f y = y) : monoFix f ha ≤ y :=
  monoFix_le_preFix f ha (le_of_eq hy)

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
