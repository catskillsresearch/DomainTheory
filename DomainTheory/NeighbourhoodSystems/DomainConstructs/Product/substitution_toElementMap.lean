/-ai
Proposition 3.7 of Scott (1981, PRG-19) states that substituting approximable maps a and b into a joint map F yields a map whose value at w is the two-variable form of F evaluated at the values of a and b at w.

Composition and pairing expand the left side to the value of F at the pairing of those two values, and the elementwise form of the two-variable map identifies that value with the right side.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMap_paired
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product.toElementMapu2082_toMapu2082

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ δ : Type*}


variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


variable {V₂ : NeighborhoodSystem γ}

open ApproximableMap


variable {V₃ : NeighborhoodSystem δ}

/-- **Proposition 3.7 (Scott 1981, PRG-19).** Multivariate approximable functions are closed under
substitution: substituting approximable maps `a, b : 𝒟₃ → 𝒟ᵢ` into a two-variable approximable map
`F : 𝒟₀ × 𝒟₁ → 𝒟₂` yields the approximable map `F ∘ ⟨a, b⟩`, whose value is `F(a(w), b(w))`. The
building blocks are exactly Definition 3.3's `paired` and Theorem 2.5's `comp`. -/
theorem substitution_toElementMap (F : ApproximableMap (prod V₀ V₁) V₂)
    (a : ApproximableMap V₃ V₀) (b : ApproximableMap V₃ V₁) (w : V₃.Element) :
    (F.comp (paired a b)).toElementMap w
      = (toMap₂ F).toElementMap₂ (a.toElementMap w) (b.toElementMap w) := by
  rw [toElementMap_comp, toElementMap_paired, toElementMap₂_toMap₂]

end DomainTheory.NeighbourhoodSystems
