/-ai
The section of an approximable map τ from a product of neighbourhood systems into the first factor, at a fixed element y of the second factor, is the approximable endomap of the first factor obtained by applying, to y, the curry of τ after a coordinate swap.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap

/-- The section `x ↦ τ(x, y)` of `τ : 𝒟₀ × 𝒟₁ → 𝒟₀` at a fixed `y`, as an approximable endomap of
`𝒟₀` (the curried `τ ∘ swap` applied to `y`). -/
def sectionX (τ : ApproximableMap (prod V₀ V₁) V₀) (y : V₁.Element) : ApproximableMap V₀ V₀ :=
  toApproxMap ((curry (τ.comp (swapC V₁ V₀))).toElementMap y)

end ApproximableMap

end DomainTheory.NeighbourhoodSystems
