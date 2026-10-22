/-ai
Multiplication of domain elements is monotone in the right argument.

A neighbourhood of the smaller right-hand element is a neighbourhood of the larger one, so the same concatenation witness serves.
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


/-- `mulElem` is monotone in its right argument. -/
theorem mulElem_mono_right (x : Ssys.Element) : Monotone (mulElem x) := by
  rintro y y' hyy' Z ⟨hInS, X, hX, Y, hY, hsub⟩
  exact ⟨hInS, X, hX, Y, hyy' Y hY, hsub⟩

end Exercise722
end DomainTheory.NeighbourhoodSystems
