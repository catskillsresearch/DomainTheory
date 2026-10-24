module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relIso
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.relSystem_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_le
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_restrict
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.restrict_embed
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.embed_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise410.le_of_embed_le

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
