/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Exercise414
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Exercise 4.21 (Scott 1981, PRG-19, Lecture IV) — `≤` as a unique fixed point; addition & multiplication

Scott asks to show that the **less-than-or-equal-to relation** `ℓ ⊆ ℕ × ℕ` is *uniquely* determined
by the fixed-point equation

  `ℓ = {(n, n) ∣ n ∈ ℕ} ∪ {(n, m⁺) ∣ (n, m) ∈ ℓ}`.

Working in the power-set domain `P(ℕ × ℕ)` (a complete lattice, Exercise 4.14), the right-hand side
is a monotone operator `leOp`. We show:

* `leRel = {(n, m) ∣ n ≤ m}` solves the equation (`leRel_isFixed`);
* the solution is **unique** (`leOp_unique`): for *any* fixed point `u` one proves, by induction on
  the second coordinate, that `(n, m) ∈ u ↔ n ≤ m`. (Unlike a general least-fixed-point situation,
  here the equation pins the relation down completely, because the clause `(n, m⁺)` never produces a
  pair with second coordinate `0`.)

Scott then considers `⟨P ℕ, ℕ, ⁺⟩` with `x⁺ = {n⁺ ∣ n ∈ x}` and the **unique function**
`[·] : ℕ → P ℕ` of 4.13(3) determined by `[0] = ℕ` and `[m⁺] = [m]⁺`. We identify it as the up-set
`[m] = {k ∣ m ≤ k}` (`upSet`), with `upSet_zero`/`upSet_succ` the two recursion equations and
`upSet_unique` their uniqueness (4.13(3)).

The structures `⟨ℕ, 0, ⁺⟩` and `⟨[m], m, ⁺⟩` are **uniquely isomorphic** via `n ↦ m + n`
(`addIso`), connecting the isomorphism with **ordinary addition** (`addIso_apply`): the unique
structure-preserving bijection sends `n` to `m + n`.

Finally, **multiplication**: the hint equation `n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` has, as its least
solution in `P ℕ`, exactly the set of multiples of `n` (`mulOp_lfp_eq_multiples`).

All set-level constructions are **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.Neighborhood.Exercise421

open DomainTheory.Neighborhood.Exercise414

/-! ### The order relation as a unique fixed point. -/

/-- Scott's operator `ℓ ↦ {(n, n)} ∪ {(n, m⁺) ∣ (n, m) ∈ ℓ}` on `P(ℕ × ℕ)`. -/
def leOp (u : Set (ℕ × ℕ)) : Set (ℕ × ℕ) :=
  {p | p.1 = p.2} ∪ {p | ∃ m, (p.1, m) ∈ u ∧ p.2 = m + 1}

/-- The relation `≤` itself, as a subset of `ℕ × ℕ`. -/
def leRel : Set (ℕ × ℕ) := {p | p.1 ≤ p.2}

/-! ### The function `[·] : ℕ → P ℕ` of 4.13(3): the up-sets. -/

/-- Scott's `x⁺ = {n⁺ ∣ n ∈ x}` on `P ℕ`. -/
def succImage (x : Set ℕ) : Set ℕ := {k | ∃ j ∈ x, k = j + 1}

/-- The up-set `[m] = {k ∣ m ≤ k}` — the value of Scott's unique function `[·]` of 4.13(3). -/
def upSet (m : ℕ) : Set ℕ := {k | m ≤ k}

/-! ### The isomorphism `⟨ℕ, 0, ⁺⟩ ≅ ⟨[m], m, ⁺⟩` is addition. -/

/-- **Exercise 4.21 (Scott 1981, PRG-19).** The structure-preserving bijection between
`⟨ℕ, 0, ⁺⟩` and `⟨[m], m, ⁺⟩` (where `[m] = {k ∣ m ≤ k}`, with distinguished element `m` and the
successor `⁺`). It is **ordinary addition** by `m`: `n ↦ m + n`. -/
def addIso (m : ℕ) : ℕ ≃ {k : ℕ // k ∈ upSet m} where
  toFun n := ⟨m + n, Nat.le_add_right m n⟩
  invFun k := k.1 - m
  left_inv n := by show m + n - m = n; omega
  right_inv := by
    rintro ⟨k, hk⟩
    exact Subtype.ext (Nat.add_sub_of_le hk)

/-! ### Multiplication via the hint fixed-point equation. -/

/-- Scott's hint operator `n·ℕ = {0} ∪ {n + m ∣ m ∈ n·ℕ}` on `P ℕ` (for fixed `n`). -/
def mulOp (n : ℕ) (u : Set ℕ) : Set ℕ := {0} ∪ {k | ∃ m ∈ u, k = n + m}
end DomainTheory.Neighborhood.Exercise421
