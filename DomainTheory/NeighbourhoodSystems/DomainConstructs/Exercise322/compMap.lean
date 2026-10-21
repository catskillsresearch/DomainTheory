/-ai
The composition mapping of Exercise 3.22 is the currying of the uncurried composition, an approximable map from the product of the two function spaces into the function space from the first domain to the third.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise322.compApp

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.22 (Scott 1981, PRG-19).** The composition mapping
`comp : (𝒟₁ → 𝒟₂) × (𝒟₀ → 𝒟₁) → (𝒟₀ → 𝒟₂)`, `comp = curry(compApp)`. -/
def compMap (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) (funSpace V₀ V₂) :=
  curry (compApp V₀ V₁ V₂)

end DomainTheory.NeighbourhoodSystems
