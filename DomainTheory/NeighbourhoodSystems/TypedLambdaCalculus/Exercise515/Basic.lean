/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
import all Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
import all Mathlib.Algebra.FreeMonoid.Basic

@[expose] public section

/-!
# Exercise 5.15 (Scott 1981, PRG-19, Lecture V) — free-semigroup powerset and Arden's lemma

> (For algebraists.) Regard `⟨{0,1}*, Λ, ·⟩` as the free semigroup on two generators. The powerset
> `P{0,1}*` is a domain (Exercise 4.17). For a word `e` set `e* = {Λ, e, e², …}`.
>
> (1) The least fixed point of `z = {e}·z ∪ {e'}` is `z = e*·{e'}`.
> (2) (David Park) The least solution of
> `x = a·x ∪ b·y ∪ c`, `y = b·x ∪ a·y ∪ d`
> is `x = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`, where `z* = Λ ∪ z*·z`.

Following Exercise 4.17, the powerset domain `P S` of a monoid `S` is the complete lattice
`(Set S, ⊆)` with pointwise product `s·t = {u·v ∣ u ∈ s, v ∈ t}` (`Set.mul`, `open Pointwise`).
Both parts are facts about the **Kleene algebra** `(Set S, ∪, ·, ∅, {1})` and hold for *any* monoid;
we prove them with `S` a general `Monoid` and specialise part (1) to `S = FreeMonoid Bool = {0,1}*`.

## Choice discipline

Mathlib's `Set`-level multiplicative lemmas (`mul_assoc`, `Set.union_mul`, `Set.mul_union`,
`Set.singleton_mul_singleton`), the order lemmas `Set.subset_iUnion`/`Set.iUnion_subset`, `Set`-power
(`pow_succ'`), `Submonoid.mem_powers_iff`, and `Monotone` over `Set` all depend on `Classical.choice`
in this toolchain (they route through `Set.image2`/`CompleteLattice` choice-using machinery). Every
*membership* iff (`Set.mem_mul`, `Set.mem_union`, `Set.mem_one`, `Set.mem_singleton_iff`) and every
*element-level* monoid lemma is choice-free. So we reprove the small slice of Kleene algebra we need
(`smul_assoc`, `sunion_mul`, `smul_union`) at the membership level, define `star` by an explicit
recursion (`kpow`) rather than `⋃ₙ zⁿ`, and phrase Arden's lemma without `Monotone` — keeping
everything **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise515

open Pointwise
open DomainTheory.NeighbourhoodSystems.Exercise414

variable {S : Type*} [Monoid S]

/-! ### A choice-free slice of Kleene algebra on `Set S` -/

/-! ### The star `z* = ⋃ₙ zⁿ`, by explicit recursion -/

/-- `zⁿ` as an iterated pointwise product (left-recursion `z^{n+1} = z·zⁿ`). -/
def kpow (z : Set S) : ℕ → Set S
  | 0 => 1
  | n + 1 => z * kpow z n

@[simp] theorem kpow_zero (z : Set S) : kpow z 0 = 1 := rfl
@[simp] theorem kpow_succ (z : Set S) (n : ℕ) : kpow z (n + 1) = z * kpow z n := rfl

/-- Scott's `z*`: the set of all finite products of elements of `z` (including the empty product
`1`). Defined as `{s ∣ ∃ n, s ∈ zⁿ}` to stay choice-free (avoiding `⋃` order lemmas). -/
def star (z : Set S) : Set S := {s | ∃ n, s ∈ kpow z n}

/-! ### Arden's lemma -/

/-- Scott's operator `w ↦ z·w ∪ v`, whose least fixed point is the least solution of `w = z·w ∪ v`. -/
def G (z v : Set S) (w : Set S) : Set S := z * w ∪ v

/-! ### Part (1): the single equation `z = {e}·z ∪ {e'}` -/

/-! ### Part (2): David Park's simultaneous system -/

/-- The "feedback" coefficient `A = a ∪ b·a*·b` of the eliminated system. -/
def parkA (a b : Set S) : Set S := a ∪ b * star a * b

/-- The "feedback" constant `C = c ∪ b·a*·d`. -/
def parkC (a b c d : Set S) : Set S := c ∪ b * star a * d

/-- Park's least solution for `x`: `x₀ = (a ∪ b·a*·b)*·(c ∪ b·a*·d)`. -/
def parkX (a b c d : Set S) : Set S := star (parkA a b) * parkC a b c d

/-- The accompanying least solution for `y`: `y₀ = a*·(b·x₀ ∪ d)`. -/
def parkY (a b c d : Set S) : Set S := star a * (b * parkX a b c d ∪ d)
end DomainTheory.NeighbourhoodSystems.Exercise515
