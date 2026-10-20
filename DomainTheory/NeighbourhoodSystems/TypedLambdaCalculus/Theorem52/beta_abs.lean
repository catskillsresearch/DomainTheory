module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem52.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2 (Scott 1981, PRG-19) — abstraction case (`inv` step).**
`(λx.λy.τ)(σ)(y) = τ[σ/x]` evaluated at `y`: the double-curry application law. The bound `y` is
carried inert past the substitution of `σ` for `x`, exactly Scott's
`(λx.λy.τ)(σ)(y) = (λx.τ)(σ)`. -/
theorem beta_abs (g : ApproximableMap (prod (prod V₀ V₁) V₂) V₃) (v : V₀.Element) (σ : V₁.Element)
    (y : V₂.Element) :
    (toApproxMap ((toApproxMap ((curry (curry g)).toElementMap v)).toElementMap σ)).toElementMap y
      = g.toElementMap (pair (pair v σ) y) := by
  rw [toElementMap_curry_apply, toElementMap_curry_apply]

end Theorem52
end DomainTheory.NeighbourhoodSystems
