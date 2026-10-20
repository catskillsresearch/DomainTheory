/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise507.curry₃

@[expose] public section

/-!
# Exercise 5.7 (Scott 1981, PRG-19, §5) — multi-variable `λ` and application from one-variable forms

Scott asks for definitions of the two-variable abstraction and application

```
λx, y. τ        and        σ(x, y)
```

that use only the *one-variable* binder `λv` and applications to *one argument at a time*, with the
combinators `p₀`, `p₁`, `pair` doing the bookkeeping. He then asks to generalise to many variables.

In the neighbourhood-system framework this is exactly the **curry/uncurry** isomorphism of
Theorem 3.12 together with **surjective pairing**:

* a two-variable function `σ : D₀ × D₁ → D₂` is applied "one argument at a time" through its curried
  form, `σ(x, y) = (curry σ)(x)(y)`; conversely `uncurry h` turns one-argument-at-a-time application
  back into a single application to a `pair`, and is *literally* built from one-argument pieces:
  `uncurry h = eval ∘ ⟨h ∘ p₀, p₁⟩` (`uncurry_eq`), using only `eval`, `p₀`, `p₁`, `pair`;
* the two-variable abstraction `λx, y. τ` is `curry`, characterised by `(curry g)(x)(y) = g⟨x, y⟩`,
  i.e. it binds one variable and returns a one-variable function;
* the projections and pairing are tied together by **surjective pairing** `⟨p₀ z, p₁ z⟩ = z`, the
  fact that makes `p₀`, `p₁`, `pair` sufficient to encode the product.

We record these as the realisations Scott requests, and give the **three-variable generalisation**
via nested currying `D₀ × (D₁ × D₂) → D₃`, illustrating the pattern for arbitrarily many variables.

No new axioms are introduced beyond the project's `Element.ext` / `ext_of_toElementMap` machinery
already used by `curry`/`uncurry`.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise507

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α β γ δ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {V₃ : NeighborhoodSystem δ}

/-! ### Surjective pairing: `p₀`, `p₁`, `pair` recover any element of the product. -/

/-! ### Application to one argument at a time. -/

/-! ### Two-variable abstraction `λx, y. τ`. -/

/-! ### Generalisation to three variables (the pattern for many variables). -/

end DomainTheory.NeighbourhoodSystems.Exercise507
