/-ai
Approximable maps are partially ordered by inclusion of their relations. Reflexivity keeps each related pair, transitivity composes two inclusions, and antisymmetry is extensionality of relations.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- Approximable maps are ordered by inclusion of their relations (Scott's approximation order on
`|𝒟₀ → 𝒟₁|`). Antisymmetry is `ApproximableMap.ext`. -/
instance : PartialOrder (ApproximableMap V₀ V₁) where
  le f g := ∀ X Y, f.rel X Y → g.rel X Y
  le_refl _ _ _ h := h
  le_trans _ _ _ h1 h2 X Y h := h2 X Y (h1 X Y h)
  le_antisymm f g h1 h2 := ApproximableMap.ext fun X Y => ⟨h1 X Y, h2 X Y⟩

end DomainTheory.NeighbourhoodSystems
