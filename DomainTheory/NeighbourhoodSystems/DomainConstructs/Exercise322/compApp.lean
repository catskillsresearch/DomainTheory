module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- The uncurried composition map `((𝒟₁→𝒟₂) × (𝒟₀→𝒟₁)) × 𝒟₀ → 𝒟₂`, `⟨⟨g, f⟩, x⟩ ↦ g(f(x))`,
built from the inner evaluation `(𝒟₀→𝒟₁) × 𝒟₀ → 𝒟₁`, the outer evaluation `(𝒟₁→𝒟₂) × 𝒟₁ → 𝒟₂`,
and the product projections/pairing (Definition 3.3). -/
def compApp (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) (V₂ : NeighborhoodSystem γ) :
    ApproximableMap (prod (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀) V₂ :=
  (evalMap V₁ V₂).comp
    (paired
      ((proj₀ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
        (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
      ((evalMap V₀ V₁).comp
        (paired
          ((proj₁ (funSpace V₁ V₂) (funSpace V₀ V₁)).comp
            (proj₀ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))
          (proj₁ (prod (funSpace V₁ V₂) (funSpace V₀ V₁)) V₀))))

end DomainTheory.NeighbourhoodSystems
