/-ai
A retraction is idempotent on elements: applying it twice to an element yields the same element as applying it once.

The element map of the composite is the composite of the element maps, and a retraction equals its composite with itself.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}


section HardDirection

variable {a : ApproximableMap E E}

/-- Idempotency of a retraction at the element level: `a(a(z)) = a(z)`. -/
theorem toElementMap_idem {a : ApproximableMap E E} (ha : IsRetraction a) (z : E.Element) :
    a.toElementMap (a.toElementMap z) = a.toElementMap z := by
  rw [← toElementMap_comp a a z, ha]

end HardDirection
end DomainTheory.NeighbourhoodSystems
