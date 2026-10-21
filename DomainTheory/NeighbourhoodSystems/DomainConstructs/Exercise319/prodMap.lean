/-ai
The product of two approximable maps is the pairing of the first map after the left projection with the second map after the right projection.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **Exercise 3.19(ii) (Scott 1981, PRG-19).** The product mapping `f × g = ⟨f ∘ p₀, g ∘ p₁⟩`. -/
def prodMap (f : ApproximableMap V₀ V₀') (g : ApproximableMap V₁ V₁') :
    ApproximableMap (prod V₀ V₁) (prod V₀' V₁') :=
  paired (f.comp (proj₀ V₀ V₁)) (g.comp (proj₁ V₀ V₁))

end DomainTheory.NeighbourhoodSystems
