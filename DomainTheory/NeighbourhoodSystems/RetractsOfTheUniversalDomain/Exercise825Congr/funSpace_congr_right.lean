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










/-- **`funSpace` congruence, codomain slot.** `𝒟₁ ≅ᴰ 𝒟₁'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀ → 𝒟₁')`. -/
theorem funSpace_congr_right (h1 : V₁ ≅ᴰ V₁') : funSpace V₀ V₁ ≅ᴰ funSpace V₀ V₁' :=
  funSpace_congr (Isomorphic.refl V₀) h1

end DomainTheory.NeighbourhoodSystems
