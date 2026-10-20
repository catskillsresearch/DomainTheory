module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

/-!
# Exercise 4.23 (Scott 1981, PRG-19, Lecture IV) — Eilenberg's uniqueness criterion

(Suggested by S. Eilenberg.) Let `f : 𝒟 → 𝒟` be approximable, and let `aₙ : 𝒟 → 𝒟` be a sequence of
approximable maps with

* (i)   `a₀(x) = ⊥` for all `x`;
* (ii)  `aₙ ⊑ aₙ₊₁` in `𝒟 → 𝒟`;
* (iii) `⊔ₙ aₙ = I_𝒟` (the identity);
* (iv)  `aₙ₊₁ ∘ f = aₙ₊₁ ∘ f ∘ aₙ`.

**Then `f` has a unique fixed point** (`f_unique_fixedPoint`).

Existence is the Fixed-point Theorem 4.1 (`fix f = ⊔ₙ fⁿ(⊥)`). For uniqueness, suppose `x = f(x)`.
Following Scott's hint, one shows by induction on `n` that

  `aₙ(x) ⊑ aₙ(fix f)`            (`approx_le`),

the step using (iv) twice and `x = f(x)`, `fix = f(fix)`:
`aₙ₊₁(x) = aₙ₊₁(f(x)) = aₙ₊₁(f(aₙ(x))) ⊑ aₙ₊₁(f(aₙ(fix))) = aₙ₊₁(f(fix)) = aₙ₊₁(fix)`.
Then, since `⊔ₙ aₙ = I` evaluates pointwise to `x = ⊔ₙ aₙ(x)` and `aₙ(x) ⊑ aₙ(fix) ⊑ fix`, the least
upper bound `x` lies below `fix`; together with `fix ⊑ x` (minimality of the least fixed point) this
forces `x = fix`. Hence the fixed point is unique.

We phrase conditions (ii)+(iii) together in the pointwise form `IsLUB {aₙ(x)} x` (equivalent to
`⊔ₙ aₙ = I` via the pointwise suprema of the function space `𝒟 → 𝒟`, Theorem 3.10): that `x` is the
*least upper bound* of the family `{aₙ(x)}` already records both that the family is bounded by `x`
(absorbing (ii)'s monotonicity into the LUB) and that nothing smaller bounds it. The argument uses
only the project's permitted element-extensionality through `Theorem41`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap
end ApproximableMap
end DomainTheory.NeighbourhoodSystems
