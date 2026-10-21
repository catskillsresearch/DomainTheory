/-ai
The product D0 × (D1 × D2) is isomorphic to (D0 × D1) × D2.

The isomorphism is the associativity order isomorphism of the element types.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-- **Exercise 3.15(ii).** `𝒟₀ × (𝒟₁ × 𝒟₂) ≅ (𝒟₀ × 𝒟₁) × 𝒟₂`. -/
theorem prod_assoc_isomorphic : prod V₀ (prod V₁ V₂) ≅ᴰ prod (prod V₀ V₁) V₂ :=
  ⟨prodAssocD V₀ V₁ V₂⟩

end DomainTheory.NeighbourhoodSystems
