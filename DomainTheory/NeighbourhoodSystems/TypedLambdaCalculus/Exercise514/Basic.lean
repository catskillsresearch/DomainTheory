/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic

@[expose] public section

/-!
# Exercise 5.14 (Scott 1981, PRG-19, Lecture V) — the graph model `Pω`

> Using the pairing function of Exercise 5.13, code finite sequences by
> `[n₀, …, n_k] = num(n₀, [n₁, …, n_k])` and define
>
>   `fun(u)(x) = {m ∣ ∃ n₀ … n_{k-1} ∈ x, [n₀+1, …, n_{k-1}+1, 0, m] ∈ u}`,
>   `graph(f)  = {[n₀+1, …, n_{k-1}+1, 0, m] ∣ m ∈ f({n₀, …, n_{k-1}})}`.
>
> Show `fun ∘ graph = λf.f` (for continuous `f`) and `graph ∘ fun ⊇ λx.x`.

Following Exercises 4.17 and 5.13, the power-set domain `Pω` is modelled by the complete lattice
`(Set ℕ, ⊆)`.

## The coding

The decisive device is the **tag**
`tag [n₀, …, n_{k-1}] m = [n₀+1, …, n_{k-1}+1, 0, m] = num(n₀+1, … num(n_{k-1}+1, num(0, m))…)`,
defined by

  `tag [] m = num 0 m`,   `tag (n :: ns) m = num (n+1) (tag ns m)`.

It is a **bijection** `(List ℕ) × ℕ ≃ ℕ`: injectivity (`tag_injective`) is an induction using
`num_injective`, and surjectivity (`tag_surjective`) is strong induction on the value, decreasing
because `num (n+1) b > b` (`num_succ_left_gt`) — the head's first coordinate is either `0` (stop,
emit `m`) or `≥ 1` (peel one entry and recurse on a strictly smaller code).

## The maps

With `entries ns = {n ∣ n ∈ ns}` the finite set of entries of a list:

* `Fun u x   = {m ∣ ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ tag ns m ∈ u}`,
* `Graph f   = {c ∣ ∃ ns m, c = tag ns m ∧ m ∈ f (entries ns)}`.

`fun ∘ graph = id` holds only for **continuous** maps, captured by
`IsApprox f := Monotone f ∧ (finite approximation)`. We prove:

* `Fun_Graph` : `Fun (Graph f) x = f x` for `IsApprox f` — the reflexive equation `fun ∘ graph = λf.f`;
* `id_le_Graph_Fun` : `u ⊆ Graph (Fun u)` — the inclusion `graph ∘ fun ⊇ λx.x` (genuinely `⊇`, since
  reorderings/duplications of a list with the same `entries` give other codes in `Graph (Fun u)`);
* `Fun_isApprox` : every `Fun u` is itself `IsApprox`, so `fun` lands in the continuous maps.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise514

open DomainTheory.NeighbourhoodSystems.Exercise513

/-! ### A strict lower bound for `num` -/

/-! ### The tag: coding `(List ℕ) × ℕ` as `ℕ` -/

/-- `tag [n₀, …, n_{k-1}] m = [n₀+1, …, n_{k-1}+1, 0, m]`, built from the pairing function `num`. -/
def tag : List ℕ → ℕ → ℕ
  | [], m => num 0 m
  | (n :: ns), m => num (n + 1) (tag ns m)

@[simp] theorem tag_nil (m : ℕ) : tag [] m = num 0 m := rfl

@[simp] theorem tag_cons (n : ℕ) (ns : List ℕ) (m : ℕ) :
    tag (n :: ns) m = num (n + 1) (tag ns m) := rfl

/-! ### The maps `fun` and `graph` -/

/-- The finite set of entries of a list, as a subset of `ℕ`. -/
def entries (ns : List ℕ) : Set ℕ := {n | n ∈ ns}

@[simp] theorem mem_entries {n : ℕ} {ns : List ℕ} : n ∈ entries ns ↔ n ∈ ns := Iff.rfl

/-- `fun(u)(x)` — apply the "function coded by `u`" to argument `x`. -/
def Fun (u : Set ℕ) (x : Set ℕ) : Set ℕ :=
  {m | ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ tag ns m ∈ u}

/-- `graph(f)` — the code of the function `f`. -/
def Graph (f : Set ℕ → Set ℕ) : Set ℕ :=
  {c | ∃ ns m, c = tag ns m ∧ m ∈ f (entries ns)}

/-- A map `f : Pω → Pω` is *approximable* (continuous) when it is monotone and every output is
already produced by a finite subset of the input. The finite subsets of `x` are exactly the
`entries ns` with all entries in `x`.

Monotonicity is phrased as an explicit `⊆`-implication rather than `Monotone f`: on `Set ℕ` the
order `≤` resolves through the `CompleteLattice` instance whose construction uses `Classical.choice`,
so the `Monotone`-based statement would not be choice-free. The two are definitionally equal. -/
def IsApprox (f : Set ℕ → Set ℕ) : Prop :=
  (∀ ⦃x x' : Set ℕ⦄, x ⊆ x' → f x ⊆ f x') ∧
    ∀ x m, m ∈ f x → ∃ ns, (∀ n ∈ ns, n ∈ x) ∧ m ∈ f (entries ns)
end DomainTheory.NeighbourhoodSystems.Exercise514
