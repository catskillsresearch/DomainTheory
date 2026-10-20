/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Theorem41

@[expose] public section

/-!
# Lecture V (§5) — Proposition 5.4 (Scott 1981, PRG-19)

Let `x`, `y`, and `τ(x, y)` have the same type `𝒟`, and let `g` range over `(𝒟 → 𝒟)`. Then the
equation

`λx. !y. τ(x, y) = !g. λx. τ(x, g(x))`

is true.

In this framework `τ : 𝒟 × 𝒟 → 𝒟` is an approximable map. We model the two sides directly:

* the **left** side `λx. !y. τ(x, y)` is `pfix τ := fix ∘ curry(τ)`, the approximable map sending
  `x` to the least fixed point of the section `y ↦ τ(x, y)` (this is `!y.τ(x,y)`, manifestly
  approximable by Theorem 4.2 — exactly Scott's appeal to 5.1 that "`f` is a function");
* the **right** side `!g. λx. τ(x, g(x))` is the least fixed point `(recOp τ).fixElement` of the
  approximable *operator* `recOp τ := curry(τ ∘ ⟨p₁, eval⟩)` on the function space, which sends a
  map `g` to `λx. τ(x, g(x))`.

The proof is Scott's: `pfix τ` is a fixed point of `recOp τ` (so `!g.… ⊑ pfix τ`), and conversely
the value `(recOp τ).fixElement (x)` is a fixed point of the section `y ↦ τ(x, y)` (so
`pfix τ (x) ⊑ (recOp τ).fixElement (x)` for every `x`). Everything is at the level of `|𝒟|` and the
function space, so the *data* (`pfix`, `recOp`) is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`); the final map equality goes through the permitted
`ext_of_toElementMap`.
-/

namespace DomainTheory.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap

/-- The section `y ↦ τ(x, y)` of `τ : 𝒟 × 𝒟 → 𝒟` at a fixed `x`, as an approximable endomap of
`𝒟` (the curried `τ` applied to `x`). -/
def section₂ (τ : ApproximableMap (prod V V) V) (x : V.Element) : ApproximableMap V V :=
  toApproxMap ((curry τ).toElementMap x)

/-- The **left-hand side** `λx. !y. τ(x, y)` of Proposition 5.4: `fix ∘ curry(τ)`. -/
def pfix (τ : ApproximableMap (prod V V) V) : ApproximableMap V V :=
  (fixMap V).comp (curry τ)

/-- The **operator** `λg. λx. τ(x, g(x))` of Proposition 5.4, as an approximable endomap of the
function space `(𝒟 → 𝒟)`: `recOp τ := curry(τ ∘ ⟨p₁, eval⟩)`. -/
def recOp (τ : ApproximableMap (prod V V) V) : ApproximableMap (funSpace V V) (funSpace V V) :=
  curry (τ.comp (paired (proj₁ (funSpace V V) V) (evalMap V V)))
end ApproximableMap
end DomainTheory.Neighborhood
