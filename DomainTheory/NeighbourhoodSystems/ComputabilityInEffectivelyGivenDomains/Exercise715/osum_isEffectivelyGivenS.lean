/-ai
If both neighbourhood systems are effectively given, and every neighbourhood of each is nonempty, their coalesced sum is effectively given in Scott's sense.

The two given presentations determine a Scott presentation of the coalesced sum.
ai-/
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


section Coalesced

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  (h₀ : ∀ X, V₀.mem X → X.Nonempty) (h₁ : ∀ Y, V₁.mem Y → Y.Nonempty)


variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)


variable {P₀ P₁}


include h₀ h₁ in
/-- **Exercise 7.15 (Scott 1981, PRG-19) — the coalesced sum `𝒟₀ ⊕ 𝒟₁` is effectively given.**
(Scott's Definition 7.1; the only classical input is the enumeration's properness branch.) -/
theorem osum_isEffectivelyGivenS (e₀ : V₀.IsEffectivelyGiven) (e₁ : V₁.IsEffectivelyGiven) :
    (osum h₀ h₁).IsEffectivelyGivenS := by
  obtain ⟨Q₀⟩ := e₀; obtain ⟨Q₁⟩ := e₁
  exact ⟨osumPresentation h₀ h₁ (P₀ := Q₀) (P₁ := Q₁)⟩

end Coalesced
end DomainTheory.NeighbourhoodSystems
