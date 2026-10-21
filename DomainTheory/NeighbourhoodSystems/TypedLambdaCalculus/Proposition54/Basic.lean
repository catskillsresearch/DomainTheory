/-ai
This file gathers and re-exports the section of τ at a fixed first coordinate, the left-hand map sending an element to the least fixed point of that section, and the recursion operator on the function space, for Proposition 5.4 (Scott 1981, PRG-19). The proposition states that the map sending x to the least fixed point in y of τ(x, y) equals the least fixed point, among endomaps g, of the operator sending g to the map x ↦ τ(x, g(x)).
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.section₂
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.pfix
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition54.recOp

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

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap



end ApproximableMap
end DomainTheory.NeighbourhoodSystems
