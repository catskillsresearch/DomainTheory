/-ai
Theorem 5.2, tuple case (Scott 1981, PRG-19), states that the map recovered from the curry of a pairing, at a context element and at x, equals the pair of the two maps recovered from the curries of the two components at that same context element and at x.

Rewrite by the curried application law, the pairing law, and the curried application law on each component.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Theorem52.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

namespace Theorem52

/-- **Theorem 5.2 (Scott 1981, PRG-19) — tuple case.**
`(λx.⟨τ₀, τ₁⟩)(σ) = ⟨(λx.τ₀)(σ), (λx.τ₁)(σ)⟩`: abstraction distributes over a tuple. -/
theorem beta_tuple (g₀ : ApproximableMap (prod V₀ V₁) V₂) (g₁ : ApproximableMap (prod V₀ V₁) V₃)
    (v : V₀.Element) (x : V₁.Element) :
    (toApproxMap ((curry (paired g₀ g₁)).toElementMap v)).toElementMap x
      = pair ((toApproxMap ((curry g₀).toElementMap v)).toElementMap x)
          ((toApproxMap ((curry g₁).toElementMap v)).toElementMap x) := by
  rw [toElementMap_curry_apply, toElementMap_paired, toElementMap_curry_apply,
    toElementMap_curry_apply]

end Theorem52
end DomainTheory.NeighbourhoodSystems
