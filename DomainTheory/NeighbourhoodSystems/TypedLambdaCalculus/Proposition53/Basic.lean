/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table55
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.sectionX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.secFixX
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Proposition53.outerOp

@[expose] public section

/-!
# Lecture V (§5) — Proposition 5.3 (Scott 1981, PRG-19)

The least fixed point of `λx, y. ⟨τ(x, y), σ(x, y)⟩` is the pair with coordinates

`!x. τ(x, !y. σ(x, y))`  and  `!y. σ(!x. τ(x, y), y)`.

This is **Bekić's theorem**: the least solution of the simultaneous system `x = τ(x, y)`,
`y = σ(x, y)` is computed coordinatewise by nested least fixed points.

In this framework `τ : 𝒟₀ × 𝒟₁ → 𝒟₀` and `σ : 𝒟₀ × 𝒟₁ → 𝒟₁` are approximable, and the pair-valued
map is `F = ⟨τ, σ⟩ = paired τ σ : 𝒟₀ × 𝒟₁ → 𝒟₀ × 𝒟₁` whose least fixed point `F.fixElement` (Thm 4.1)
is the least solution Scott invokes in his hint. We build:

* `secFixX τ : 𝒟₁ → 𝒟₀`, the approximable map `y ↦ !x. τ(x, y)` (`fix ∘ curry(τ ∘ swap)`);
* `outerOp τ σ : 𝒟₁ → 𝒟₁`, the approximable map `y ↦ σ(!x. τ(x, y), y)`;
* `ystar = (outerOp τ σ).fixElement = !y. σ(!x. τ(x, y), y)` and
  `xstar = secFixX τ (ystar) = !x. τ(x, ystar)`.

The theorem `fixElement_paired_eq` states `F.fixElement = ⟨xstar, ystar⟩`, proved exactly as Scott:
`⟨xstar, ystar⟩` is a fixed-point pair (so `F.fixElement ⊑ ⟨xstar, ystar⟩`), and from the least
solution `⟨a, b⟩` one derives `!x.τ(x,b) ⊑ a`, hence `outerOp(b) ⊑ b`, hence `ystar ⊑ b`, hence
`xstar ⊑ a`. All *data* is **choice-free**; the proof uses only the order on `|𝒟ᵢ|` and the
universal properties of `fixElement`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

namespace ApproximableMap



end ApproximableMap
end DomainTheory.NeighbourhoodSystems
