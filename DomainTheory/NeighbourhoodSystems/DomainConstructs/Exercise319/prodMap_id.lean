/-ai
The product of the two identity maps is the identity map of the product.

Two maps agree when they induce the same map of elements. Rewrite by the element formula for a product of maps and by the element formula for an identity, and then pair the two components of the element to recover it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.toElementMap_prodMap

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}



/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves identities: `I × I = I`. -/
theorem prodMap_id : prodMap (idMap V₀) (idMap V₁) = idMap (prod V₀ V₁) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_idMap, toElementMap_idMap, toElementMap_idMap,
    pair_fst_snd]

end DomainTheory.NeighbourhoodSystems
