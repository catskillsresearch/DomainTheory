/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise118
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41

@[expose] public section

/-!
# Exercise 4.13 (Scott 1981, PRG-19, Lecture IV) — eliminating the circularity

The proof of Theorem 4.1 uses the integers (the chain `fⁿ(⊥)`), whereas the proof of Theorem 4.6
uses 4.1 — *a hint of circularity*. Scott shows it can be eliminated:

**(1)** If a domain `𝒟` has an element `a` where, for `f : 𝒟 → 𝒟`, the relation `f(a) ⊑ a` holds,
then the least fixed point can be defined *without* the integers, purely by a greatest-lower-bound:

  `fix(f) = ⋂ {x ∈ |𝒟| ∣ f(x) ⊑ x}`,

and `fix(f) ⊑ a`. Here `b = ⋂{…}` is a well-defined element by Exercise 1.18 (`sInf`, the
intersection of a non-empty family of filters). The argument uses **only the monotonicity** of
`f : |𝒟| → |𝒟|` — no directed sups, no integers:

* `f(b) ⊑ x` whenever `f(x) ⊑ x` (since `b ⊑ x` so `f(b) ⊑ f(x) ⊑ x`), hence `f(b) ⊑ b`;
* then `f(f(b)) ⊑ f(b)`, so `b ⊑ f(b)` too; thus `b = f(b)`;
* `b` is least among pre-fixed points, in particular the least fixed point.

This is `monoFix` / `monoFix_isFixed` / `monoFix_least` / `monoFix_le_preFix` below. It is entirely
**choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).

**(2)** The argument uses only monotonicity, and `(1)` *always* applies to power-set domains `P A`
(take `a = A`, the top element, where `f(A) ⊑ A` is automatic) — see Exercise 4.14.

**(3)** With `(1)` one re-establishes the recursion principle behind 4.6 directly: for any structured
set `⟨Z, z, ·⟩` there is a *unique* `s : ℕ → Z` with `s(0) = z` and `s(n⁺) = s(n)·`
(`exists_unique_nat_rec`). This is the choice-free primitive recursion theorem; combined with `(1)`
it removes the circularity (one no longer needs 4.1 to build the iteration).

**(4)** Specializing `(3)` to `⟨ℕ, 0, ⁺⟩` recovers the very iteration `n ↦ fⁿ` used in 4.1
(`nat_iterate_unique`), closing the loop without circularity.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*} {V : NeighborhoodSystem α}

namespace NeighborhoodSystem

/-! ### (1) The least fixed point of a monotone map via intersection. -/

/-- The set of *pre-fixed points* `{x ∣ f(x) ⊑ x}` of `f`. -/
def preFix (f : V.Element → V.Element) : Set V.Element := {x | f x ≤ x}

@[simp] theorem mem_preFix {f : V.Element → V.Element} {x : V.Element} :
    x ∈ preFix f ↔ f x ≤ x := Iff.rfl

/-- **Exercise 4.13(1) (Scott 1981, PRG-19).** The least fixed point of a *monotone* `f` defined
purely as the greatest lower bound of the pre-fixed points, `⋂ {x ∣ f(x) ⊑ x}`. Well-defined as an
element by Exercise 1.18 (`sInf`); the non-emptiness witness is any `a` with `f(a) ⊑ a`. -/
def monoFix (f : V.Element → V.Element) {a : V.Element} (ha : f a ≤ a) : V.Element :=
  V.sInf (preFix f) ⟨a, ha⟩

/-! ### (3) The primitive-recursion theorem (choice-free), behind 4.6. -/

/-! ### (4) Specialization to `⟨ℕ, 0, ⁺⟩`. -/
end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
