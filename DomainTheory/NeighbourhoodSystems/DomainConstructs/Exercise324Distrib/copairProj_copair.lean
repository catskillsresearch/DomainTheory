module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_comp_inMapu2080
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise324Distrib.copair_comp_inMapu2081

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}





/-- **Exercise 3.24(iv) (Scott 1981, PRG-19).** `(𝒟₀→𝒟₂) × (𝒟₁→𝒟₂)` is a **retract** of
`(𝒟₀+𝒟₁) → 𝒟₂`: the copairing is a section of `h ↦ (h∘in₀, h∘in₁)`. (It is *not* an isomorphism: the
value of a map on the basepoint `Λ` is not recoverable from its restrictions to the two copies.) -/
theorem copairProj_copair (a : ApproximableMap V₀ V₂) (b : ApproximableMap V₁ V₂) :
    copairProj (h₀ := h₀) (h₁ := h₁) (copair a b) = (a, b) := by
  show ((copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₀,
        (copair (h₀ := h₀) (h₁ := h₁) a b).comp inMap₁) = (a, b)
  rw [copair_comp_inMap₀, copair_comp_inMap₁]

end DomainTheory.NeighbourhoodSystems
