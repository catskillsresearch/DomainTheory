/-ai
The product of the embedding of a word with the infinite word of that word equals the infinite word.

Rewrite the product as the action of prepending, and apply the fixed-point equation of that approximable map.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import Mathlib.Data.Set.Insert
import all Mathlib.Data.Set.Insert
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722.prependMap_toElementMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open NeighborhoodSystem ApproximableMap




























/-- **`σ⃗ = σ·σ⃗`** (Scott's defining equation), unconditionally. -/
theorem streamArrow_eq (σ : List Bool) :
    mulElem (emb σ) (streamArrow σ) = streamArrow σ := by
  rw [← prependMap_toElementMap]
  exact toElementMap_fixElement (prependMap σ)

end Exercise722
end DomainTheory.NeighbourhoodSystems
