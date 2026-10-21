/-ai
The infinite word of a word equals its square.

The square lies below the infinite word, and the infinite word lies below the square.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamArrow_le_mul_self
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.streamArrow_mul_self_le

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap


/-- **Exercise 7.22l (Scott's first equation, unconditional).** `σ⃗·σ⃗ = σ⃗`, for the genuine
least-fixed-point `σ⃗`, with no side-condition. -/
theorem streamArrow_mul_self (σ : List Bool) :
    mulElem (streamArrow σ) (streamArrow σ) = streamArrow σ :=
  le_antisymm (streamArrow_mul_self_le σ) (streamArrow_le_mul_self σ)

end Exercise722
end DomainTheory.NeighbourhoodSystems
