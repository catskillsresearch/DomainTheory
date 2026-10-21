/-ai
The element map of a product of approximable maps sends a product element to the pair of the images of its two components.

Unfold the product map as a pairing of composites with the projections. The element map of a pairing is the pair of the element maps, composition acts through composition of element maps, and the element maps of the two projections are the two components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.19 (Scott 1981, PRG-19).** `(f × g)(w) = ⟨f(w₀), g(w₁)⟩` for every product element
`w` (so in particular `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`, equation (i)). -/
theorem toElementMap_prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁')
    (w : (prod V₀ V₁).Element) :
    (prodMap f g).toElementMap w = pair (f.toElementMap w.fst) (g.toElementMap w.snd) := by
  rw [prodMap, toElementMap_paired, toElementMap_comp, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁]

end DomainTheory.NeighbourhoodSystems
