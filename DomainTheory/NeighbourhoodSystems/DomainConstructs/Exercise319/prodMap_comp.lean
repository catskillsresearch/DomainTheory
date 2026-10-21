/-ai
The product of approximable maps preserves composition: the product of two composites equals the composite of the two products.

Two maps agree when they induce the same map of elements. Rewrite by the element formula for a product of maps, by the element formula for composition, and by the two components of a pair, so that both sides send a product element to the pair of the two iterated images of its components.
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


/-- **Exercise 3.20 (Scott 1981, PRG-19).** `×` preserves composition:
`(f' ∘ f) × (g' ∘ g) = (f' × g') ∘ (f × g)`. -/
theorem prodMap_comp {α'' β'' : Type*} {V₀'' : NeighborhoodSystem α''} {V₁'' : NeighborhoodSystem β''}
    (f' : ApproximableMap V₀' V₀'') (f : ApproximableMap V₀ V₀')
    (g' : ApproximableMap V₁' V₁'') (g : ApproximableMap V₁ V₁') :
    prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g) := by
  apply ext_of_toElementMap
  intro w
  rw [toElementMap_prodMap, toElementMap_comp, toElementMap_comp, toElementMap_comp,
    toElementMap_prodMap, toElementMap_prodMap, fst_pair, snd_pair]

end DomainTheory.NeighbourhoodSystems
