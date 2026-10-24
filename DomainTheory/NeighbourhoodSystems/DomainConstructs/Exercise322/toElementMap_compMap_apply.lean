module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.compApp
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.compMap
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.toElementMap_compApp

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}


/-- **Exercise 3.22 (Scott 1981, PRG-19).** `comp(g, f) = g ∘ f`: applying the value
`comp(⟨g, f⟩) ∈ |𝒟₀ → 𝒟₂|` to `x` gives `g(f(x))`. -/
theorem toElementMap_compMap_apply (Gφ : (funSpace V₁ V₂).Element) (Fφ : (funSpace V₀ V₁).Element)
    (x : V₀.Element) :
    (toApproxMap ((compMap V₀ V₁ V₂).toElementMap (pair Gφ Fφ))).toElementMap x
      = (toApproxMap Gφ).toElementMap ((toApproxMap Fφ).toElementMap x) := by
  rw [compMap, toElementMap_curry_apply, toElementMap_compApp]

end DomainTheory.NeighbourhoodSystems
