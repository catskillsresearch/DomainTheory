/-ai
The value of the composition map at a pair of elements, read back as an approximable map, is the composition of the two approximable maps.

The two maps agree on elements by the elementwise computation of the composition and the element map of a composite.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.toElementMap_compMap_apply

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 3.22 (Scott 1981, PRG-19).** The relational form `comp(g, f) = g ∘ f`: the value of
`comp` at `⟨g, f⟩`, read back as an approximable map, is the composition of the approximable maps. -/
theorem toApproxMap_compMap (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element) :
    toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))
      = (toApproxMap Gφ).comp (toApproxMap Fφ) := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_compMap_apply, toElementMap_comp]

end DomainTheory.NeighbourhoodSystems
