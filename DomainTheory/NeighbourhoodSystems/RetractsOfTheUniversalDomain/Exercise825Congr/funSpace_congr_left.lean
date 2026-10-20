module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810b
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Congr.funSpace_congr

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}










/-- **`funSpace` congruence, domain slot.** `𝒟₀ ≅ᴰ 𝒟₀'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁)`. -/
theorem funSpace_congr_left (h0 : V₀ ≅ᴰ V₀') : funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁ :=
  funSpace_congr h0 (Isomorphic.refl V₁)

end DomainTheory.NeighbourhoodSystems
