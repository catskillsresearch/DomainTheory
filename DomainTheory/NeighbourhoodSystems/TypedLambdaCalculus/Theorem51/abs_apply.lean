module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem51


/-- **Theorem 5.1, abstraction case (Scott 1981, PRG-19).** If `⟦σ⟧ : Γ × 𝒟ₙ → 𝒟'` is approximable,
then `λx.σ` is interpreted by `curry ⟦σ⟧ : Γ → (𝒟ₙ → 𝒟')` (approximable by Thm 3.12), with value
`(λx.σ)(v)(x) = σ(v, x)`. -/
theorem abs_apply (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

end Theorem51
end DomainTheory.NeighbourhoodSystems
