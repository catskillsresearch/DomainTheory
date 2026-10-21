/-ai
Every element of a product is the pair of its two projections.

Rewrite by the action of the two projections and by pairing the first and second components.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}


/-- **Surjective pairing.** Every element `z : D₀ × D₁` is recovered from its projections:
`⟨p₀(z), p₁(z)⟩ = z`. This is what makes `p₀`, `p₁`, `pair` enough to encode the product. -/
theorem surjective_pairing (z : (prod V₀ V₁).Element) :
    pair ((proj₀ V₀ V₁).toElementMap z) ((proj₁ V₀ V₁).toElementMap z) = z := by
  rw [toElementMap_proj₀, toElementMap_proj₁, pair_fst_snd]

end DomainTheory.NeighbourhoodSystems.Exercise507
