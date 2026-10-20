/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

/-!
# Exercise 4.9 (Scott 1981, PRG-19, Lecture IV) — the operator `Ψ` and `fix = fix(Ψ)`

Scott asks for an *approximable* operator

  `Ψ : ((𝒟 → 𝒟) → 𝒟) → ((𝒟 → 𝒟) → 𝒟)`     with     `Ψ(θ)(f) = f(θ(f))`,

and then to prove that `fix : (𝒟 → 𝒟) → 𝒟` is the **least fixed point** of `Ψ` — the true equation
`fix = fix(λF λf. f(F(f)))` (cf. the text following Exercise 4.9).

**Construction.** Writing `G = (𝒟 → 𝒟)` and `E = (G → 𝒟)`, the term `λF λf. f(F(f))` is built from the
cartesian-closed combinators: `Ψ = curry Φ` where `Φ : E × G → 𝒟` is
`Φ = eval_{𝒟,𝒟} ∘ ⟨π_G, eval_{G,𝒟}⟩`, sending `⟨F, f⟩ ↦ f(F(f))`. Approximability is automatic
(`bigPsi`); the defining equation `Ψ(θ)(f) = f(θ(f))` is `bigPsi_apply` (Theorem 3.12's `curry` β-rule
plus the `eval`/projection laws).

**`fix = fix(Ψ)`.** Representing `fix` as the element `toFilter (fixMap V) ∈ |E|`:

* `bigPsi_fix` — `Ψ(fix) = fix`: indeed `Ψ(fix)(f) = f(fix(f)) = f(fix f) = fix f = fix(f)` since
  `fix(f) = fix f` is a fixed point of `f` (Theorem 4.1);
* `bigPsi_least` — if `Ψ(θ) ⊑ θ` then `fix ⊑ θ`: pointwise, `Ψ(θ)(f) = f(θ(f)) ⊑ θ(f)` makes `θ(f)`
  a pre-fixed point of `f`, so `fix f ⊑ θ(f)` (Theorem 4.1's minimality), i.e. `fix(f) ⊑ θ(f)`;
* `fix_eq_fixElement_bigPsi` — combining the two, `fix = fix(Ψ)` (`= fixElement Ψ`, Theorem 4.1's
  canonical least fixed point).

The operator data `bigPsi` is **choice-free**; equalities of elements/operators go through the
project's permitted `Element.ext` / `ext_of_toElementMap`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- **Exercise 4.9 (Scott 1981, PRG-19).** The approximable operator `Ψ = λF λf. f(F(f))` on the
higher-order domain `E = ((𝒟 → 𝒟) → 𝒟)`, built as `curry (eval ∘ ⟨π_G, eval⟩)`. -/
def bigPsi (V : NeighborhoodSystem α) :
    ApproximableMap (funSpace (funSpace V V) V) (funSpace (funSpace V V) V) :=
  curry ((evalMap V V).comp
    (paired (proj₁ (funSpace (funSpace V V) V) (funSpace V V)) (evalMap (funSpace V V) V)))
end DomainTheory.NeighbourhoodSystems
