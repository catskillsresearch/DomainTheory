/-ai
The exponential adjunction of Exercise 3.23 identifies approximable maps from a product into a domain with approximable maps from the first factor into the function space of the second factor and the codomain, by the curry equivalence.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.BasicInst4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise323.BasicInst5

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} (V : NeighborhoodSystem α)

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.23 (Scott 1981, PRG-19).** The cartesian-closed adjunction
`Hom(𝒟₀ × 𝒟₁, 𝒟₂) ≃o Hom(𝒟₀, (𝒟₁ → 𝒟₂))`, exhibiting `(𝒟₁ → 𝒟₂)` as the exponential object. This
is exactly `curryEquiv` of Theorem 3.12. -/
def homAdjunction (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod V₀ V₁) V₂ ≃o ApproximableMap V₀ (funSpace V₁ V₂) :=
  curryEquiv V₀ V₁ V₂

end DomainTheory.NeighbourhoodSystems
