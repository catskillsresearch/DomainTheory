/-ai
The comparison of a map out of a separated sum with maps out of the two summands sends the map to the pair of its composites with the two injections.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}

/-- The canonical comparison `Hom(𝒟₀+𝒟₁, 𝒟₂) → Hom(𝒟₀,𝒟₂) × Hom(𝒟₁,𝒟₂)`, `h ↦ (h∘in₀, h∘in₁)`. -/
def copairProj (h : ApproximableMap (sum V₀ V₁ h₀ h₁) V₂) :
    ApproximableMap V₀ V₂ × ApproximableMap V₁ V₂ :=
  (h.comp inMap₀, h.comp inMap₁)

end DomainTheory.NeighbourhoodSystems
