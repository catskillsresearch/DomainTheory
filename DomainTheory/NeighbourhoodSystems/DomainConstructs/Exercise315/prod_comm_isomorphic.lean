/-ai
The product D0 × D1 is isomorphic to D1 × D0.

The isomorphism is the commutativity order isomorphism of the element types.
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







/-- **Exercise 3.15(i).** `𝒟₀ × 𝒟₁ ≅ 𝒟₁ × 𝒟₀`. -/
theorem prod_comm_isomorphic : prod V₀ V₁ ≅ᴰ prod V₁ V₀ := ⟨prodCommD V₀ V₁⟩

end DomainTheory.NeighbourhoodSystems
