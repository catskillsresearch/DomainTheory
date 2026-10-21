/-ai
This file gathers and re-exports Theorem 6.9, Proposition 6.7, Lemma 6.15, and Exercise 4.08, the ingredients of Scott's Theorem 6.16: if a functor on domains and strict approximable maps is continuous on maps and D is an initial algebra, then D embeds in every solution of the domain equation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition67
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise408

@[expose] public section

/-!
# Lecture VI — Theorem 6.16 (Scott 1981, PRG-19): an initial algebra embeds in every solution

> **THEOREM 6.16.** If on the category of domains and strict approximable maps the functor `T` is
> continuous on maps, and if `D` is an initial `T`-algebra, then for any system `E ≅ T(E)` we have
> `D ⊴ E`.

Scott's proof. By Theorem 6.9 there is a homomorphism `h : D → E` and (running 6.9 the other way) a
homomorphism `g : E → D`. The composite `g ∘ h : D → D` is a homomorphism of the *initial* algebra
`D`, hence equals `I_D` by uniqueness. By Lemma 6.15 it remains to show `h ∘ g ⊑ I_E`.

Writing `i : T(D) → D`, `j : D → T(D)` for `D`'s isomorphism (Lambek, Proposition 6.7) and
`u : T(E) → E`, `v : E → T(E)` for `E`'s, the proof of 6.9 produces `h` and `g` as the least fixed
points of
`h = u ∘ T(h) ∘ j` and `g = i ∘ T(g) ∘ v`.
Setting `h₀ = ⊥`, `g₀ = ⊥` and `hₙ₊₁ = u ∘ T(hₙ) ∘ j`, `gₙ₊₁ = i ∘ T(gₙ) ∘ v`, one computes
`hₙ₊₁ ∘ gₙ₊₁ = u ∘ T(hₙ ∘ gₙ) ∘ v` (using `j ∘ i = I_{T(D)}`), so `kₙ := hₙ ∘ gₙ` is the approximant
chain of the operator `k ↦ u ∘ T(k) ∘ v`. Therefore `h ∘ g = ⊔ₙ (hₙ ∘ gₙ)` is its *least* fixed
point, and since `I_E` is a fixed point of that operator, `h ∘ g ⊑ I_E`.

## What the formalization does

Everything reuses Theorem 6.9's operator `(homOp T D E j k) ∘ Φ` on Scott's **strict** function
space `(D →⊥ E)` (Exercise 5.10). The per-step computation is isolated as `opStep`. The three
approximant chains `H`, `G`, `K` (for `h`, `g`, `k`) and the ladder identity `H n ∘ G n = K n` give
`h ∘ g = k` (the least fixed point of `u ∘ T(·) ∘ v`), which is `⊑ I_E` because `I_E` is a fixed
point. Lemma 6.15 (`trianglelefteq_of_projectionPair`) then closes `D ⊴ E`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510


/-! ### General helpers. -/

/-! ### Theorem 6.16. -/
end DomainTheory.NeighbourhoodSystems
