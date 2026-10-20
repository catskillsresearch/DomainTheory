/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319.prodMap

@[expose] public section

/-!
# Exercise 3.19 / 3.20 (Scott 1981, PRG-19, §3) — the product functor `f × g`

Given approximable mappings `f : 𝒟₀ → 𝒟₀'` and `g : 𝒟₁ → 𝒟₁'`, Scott's Exercise 3.19 constructs
the product mapping `f × g : 𝒟₀ × 𝒟₁ → 𝒟₀' × 𝒟₁'` with

* **(i)** `(f × g)(⟨x, y⟩) = ⟨f(x), g(y)⟩`, and
* **(ii)** `f × g = ⟨f ∘ p₀, g ∘ p₁⟩`.

We take (ii) as the definition (`prodMap`, built from Definition 3.3's `paired`/`proj`), and prove
(i) — indeed the more general `toElementMap_prodMap` (`(f × g)(w) = ⟨f(w₀), g(w₁)⟩`).

Exercise 3.20 (for category theorists) then follows: `×` is a **functor** (`prodMap_id`,
`prodMap_comp`), and `prod` with its projections is the **categorical product** — the universal
property `paired`/`proj` with uniqueness `paired_unique`.

The sum functor `f + g` is treated in `Exercise318.lean`/`Exercise319Sum.lean` after the sum system
is built. Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}


/-! ### Exercise 3.20 — `×` is a functor. -/

/-! ### Exercise 3.20 — `prod` is the categorical product. -/
end DomainTheory.NeighbourhoodSystems
