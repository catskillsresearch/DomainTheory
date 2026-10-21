/-ai
The left projection after a pairing is the left factor, and the right projection after a pairing is the right factor.

The two identities are the corresponding lemmas on a projection after a pairing.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}




/-- **Exercise 3.20 (Scott 1981, PRG-19).** The universal property of the product (existence):
`p₀ ∘ ⟨h₀, h₁⟩ = h₀` and `p₁ ∘ ⟨h₀, h₁⟩ = h₁` (these are Proposition 3.4(i)). -/
theorem proj_paired (h₀ : ApproximableMap V₂ V₀) (h₁ : ApproximableMap V₂ V₁) :
    (proj₀ V₀ V₁).comp (paired h₀ h₁) = h₀ ∧ (proj₁ V₀ V₁).comp (paired h₀ h₁) = h₁ :=
  ⟨proj₀_comp_paired h₀ h₁, proj₁_comp_paired h₀ h₁⟩

end DomainTheory.NeighbourhoodSystems
