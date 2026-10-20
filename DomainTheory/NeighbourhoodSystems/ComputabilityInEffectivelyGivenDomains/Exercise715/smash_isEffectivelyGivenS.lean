module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise510
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise316
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise715.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*}








open Exercise510

section Smash

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}







variable (P₀ P₁)




/-- **Exercise 7.15 (Scott 1981, PRG-19) — the smash product `𝒟₀ ⊗ 𝒟₁` is effectively given.**
(Scott's Definition 7.1; the only classical input is the enumeration's properness branch.) -/
theorem smash_isEffectivelyGivenS (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (smash V₀ V₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := h₀; obtain ⟨Q₁⟩ := h₁
  exact ⟨smashPresentation Q₀ Q₁⟩

end Smash
end DomainTheory.NeighbourhoodSystems
