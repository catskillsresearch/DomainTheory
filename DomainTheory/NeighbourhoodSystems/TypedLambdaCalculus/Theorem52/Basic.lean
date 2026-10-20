module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55

@[expose] public section

/-!
# Lecture V (§5) — Theorem 5.2 (Scott 1981, PRG-19)

**Theorem 5.2.** For suitably typed `λ`-terms the following equation is true:

`(λx₀, …, xₙ₋₁. τ)(σ₀, …, σₙ₋₁) = τ[σ₀/x₀, …, σₙ₋₁/xₙ₋₁].`

This is the fundamental **conversion (β-substitution) rule**. Scott proves it by induction on `τ`,
reducing to the one-variable case and using three "true equations" along the way. In the
neighbourhood-system framework, where a term-in-context is an approximable map, the one-variable
rule is exactly the computation law of `curry`/`eval` from Theorem 3.12, and the inductive helper
equations are the corresponding combinator identities:

* **β (one variable, in context).** With `⟦τ⟧ = g : Γ × 𝒟ₓ → 𝒟'`, the term `λx.τ` is `curry g` and
  applying it to a constant `σ` substitutes `σ` for `x`:
  `eval ∘ ⟨curry g, const σ⟩ = g ∘ ⟨I, const σ⟩`   (`beta`).
* **tuple.** `(λx.⟨τ₀, τ₁⟩)(σ) = ⟨(λx.τ₀)(σ), (λx.τ₁)(σ)⟩`   (`beta_tuple`).
* **abstraction (Scott's `inv` step).** `(λx.λy.τ)(σ)(y) = τ[σ/x]` evaluated, i.e. the double-curry
  application law   (`beta_abs`).

The base value law `(λx.τ)(σ) = τ[σ/x]` evaluated pointwise is `toElementMap_curry_apply`.
Everything here is at the level of approximable maps; the *map equation* `beta` uses the permitted
`ext_of_toElementMap`, the *value* equations are choice-free.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₃ : NeighborhoodSystem δ}

namespace Theorem52
end Theorem52
end DomainTheory.NeighbourhoodSystems
