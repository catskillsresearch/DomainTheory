/-ai
The neighbourhood system on binary words is positive.

A neighbourhood intersection yields a nonempty intersection, and a nonempty intersection of two members lies in the family by the intersection constructor.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap


/-- `S` is indeed positive (Exercise 1.19's `IsPositive`). -/
theorem Ssys_isPositive : Ssys.IsPositive := by
  intro X Y hX hY
  exact ⟨fun h => h.nonempty, fun h => InS.inter hX hY h⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
