/-ai
The order isomorphism of Exercise 3.24(i) sends an approximable map into a product to the pair of its composites with the two projections, and sends a pair of maps back by pairing them. The two directions invert by the pairing and projection round trips. An inequality of both projected composites reassembles, through those round trips, into an inequality of the original maps, because a relation of the paired map splits into the two projected relations. An inequality of maps passes to each projected composite along the intermediate neighbourhood of the projection relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The order-isomorphism on approximable maps
`Hom(𝒟₀, 𝒟₁ × 𝒟₂) ≃o Hom(𝒟₀, 𝒟₁) × Hom(𝒟₀, 𝒟₂)`, `h ↦ (p₀ ∘ h, p₁ ∘ h)`. -/
def funProdEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap V₀ (prod V₁ V₂) ≃o (ApproximableMap V₀ V₁ × ApproximableMap V₀ V₂) where
  toFun h := ((proj₀ V₁ V₂).comp h, (proj₁ V₁ V₂).comp h)
  invFun p := paired p.1 p.2
  left_inv h := paired_proj h
  right_inv p := by
    ext1
    · exact proj₀_comp_paired p.1 p.2
    · exact proj₁_comp_paired p.1 p.2
  map_rel_iff' := by
    intro h h'
    constructor
    · rintro ⟨h0, h1⟩
      rw [← paired_proj h, ← paired_proj h']
      intro Z P hrel
      obtain ⟨hP, hfP, hgP⟩ := hrel
      exact ⟨hP, h0 _ _ hfP, h1 _ _ hgP⟩
    · intro hle
      refine ⟨fun X Y hrel => ?_, fun X Y hrel => ?_⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩

end DomainTheory.NeighbourhoodSystems
