/-ai
The triple product of the infinite word of a word equals the infinite word.

Rewrite twice by the equation that the infinite word equals its square.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamArrow_mul_self

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **Scott's second equation.** `σ⃗·σ⃗·σ⃗ = σ⃗`. -/
theorem streamArrow_mul_self_self (σ : List Bool) :
    mulElem (mulElem (streamArrow σ) (streamArrow σ)) (streamArrow σ) = streamArrow σ := by
  rw [streamArrow_mul_self, streamArrow_mul_self]

end Exercise722
end DomainTheory.NeighbourhoodSystems
