module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2, base value law (Scott 1981, PRG-19).** `(λx.τ)(σ) = τ[σ/x]` evaluated: applying
the abstraction `curry g` (in free-variable context `v`) to `x` substitutes, giving `g(v, x)`. -/
theorem subst_value (g : ApproximableMap (prod V₀ V₁) V₂) (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry g).toElementMap v)).toElementMap x = g.toElementMap (pair v x) :=
  toElementMap_curry_apply g v x

end Theorem52
end DomainTheory.NeighbourhoodSystems
