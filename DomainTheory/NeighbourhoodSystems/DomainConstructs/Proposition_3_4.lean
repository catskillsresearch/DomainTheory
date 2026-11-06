module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.ProjectionMappings

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem
open ApproximableMap

variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₂ : NeighborhoodSystem γ}

/-- Scott's Proposition 3.4: projections invert pairing, pairing recovers maps into products,
    and pairing acts elementwise by pairing the images. -/
theorem proposition_3_4 :
    (∀ (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁),
      (proj₀ V₀ V₁).comp (paired f g) = f ∧ (proj₁ V₀ V₁).comp (paired f g) = g) ∧
    (∀ (h : ApproximableMap V₂ (prod V₀ V₁)),
      paired ((proj₀ V₀ V₁).comp h) ((proj₁ V₀ V₁).comp h) = h) ∧
    (∀ (f : ApproximableMap V₂ V₀) (g : ApproximableMap V₂ V₁) (w : V₂.Element),
      (paired f g).toElementMap w = pair (f.toElementMap w) (g.toElementMap w)) :=
  ⟨fun f g => ⟨proj₀_comp_paired f g, proj₁_comp_paired f g⟩, paired_proj, toElementMap_paired⟩

end DomainTheory.NeighbourhoodSystems
