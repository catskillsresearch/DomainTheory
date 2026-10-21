/-ai
Currying, as in Theorem 3.12, is a domain isomorphism: the function space from a product is isomorphic to the iterated function space.

The witness is the currying order isomorphism.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}











/-- **Currying (Theorem 3.12), as a domain isomorphism.** `(𝒟₀ × 𝒟₁ → 𝒟₂) ≅ (𝒟₀ → (𝒟₁ → 𝒟₂))`. -/
theorem curry_isomorphic (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    funSpace (prod V₀ V₁) V₂ ≅ᴰ funSpace V₀ (funSpace V₁ V₂) :=
  ⟨curryIso V₀ V₁ V₂⟩

end DomainTheory.NeighbourhoodSystems
