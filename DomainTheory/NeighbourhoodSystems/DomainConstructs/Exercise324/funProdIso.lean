module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324.funProdEquiv

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)|`. -/
def funProdIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    (funSpace V₀ (prod V₁ V₂)).Element ≃o (prod (funSpace V₀ V₁) (funSpace V₀ V₂)).Element :=
  (funSpaceEquiv V₀ (prod V₁ V₂)).trans <|
    (funProdEquiv V₀ V₁ V₂).trans <|
      (prodCongrOrderIso (funSpaceEquiv V₀ V₁).symm (funSpaceEquiv V₀ V₂).symm).trans
        (prodEquiv (funSpace V₀ V₁) (funSpace V₀ V₂)).symm

end DomainTheory.NeighbourhoodSystems
