/-ai
An approximable map of two variables is a ternary relation on sets such that related sets are neighbourhoods of the two domains and of the codomain, the three master neighbourhoods are related, a pair of inputs related to two outputs is related to their intersection, and the relation persists when both inputs are replaced by smaller neighbourhoods and the output by a larger neighbourhood.
ai-/
module


public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Approximable
public import Mathlib.Data.Set.Image

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α β γ : Type*}

/-- **Exercise 2.19 (Scott 1981, PRG-19).** An *approximable mapping of two variables*
`f : 𝒟₀ × 𝒟₁ → 𝒟₂` is a ternary relation `X, Y f Z` confined to `𝒟₀ × 𝒟₁ × 𝒟₂` with the natural
generalization of Definition 2.1: (i) `Δ₀, Δ₁ f Δ₂`; (ii) intersectivity on the output; (iii)
monotonicity jointly in both inputs (sharper) and the output (blunter). -/
structure ApproximableMap₂ (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) where
  /-- The underlying ternary relation `X, Y f Z`. -/
  rel : Set α → Set β → Set γ → Prop
  rel_dom₀ : ∀ {X Y Z}, rel X Y Z → V₀.mem X
  rel_dom₁ : ∀ {X Y Z}, rel X Y Z → V₁.mem Y
  rel_cod : ∀ {X Y Z}, rel X Y Z → V₂.mem Z
  /-- (i) `Δ₀, Δ₁ f Δ₂`. -/
  master_rel : rel V₀.master V₁.master V₂.master
  /-- (ii) intersectivity on the output. -/
  inter_right : ∀ {X Y Z Z'}, rel X Y Z → rel X Y Z' → rel X Y (Z ∩ Z')
  /-- (iii) joint monotonicity: sharper inputs `X' ⊆ X`, `Y' ⊆ Y`; blunter output `Z ⊆ Z'`. -/
  mono : ∀ {X X' Y Y' Z Z'}, rel X Y Z → X' ⊆ X → Y' ⊆ Y → Z ⊆ Z' →
    V₀.mem X' → V₁.mem Y' → V₂.mem Z' → rel X' Y' Z'

end DomainTheory.NeighbourhoodSystems
