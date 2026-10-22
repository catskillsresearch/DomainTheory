/-ai
This file gathers and re-exports the coding and the two maps of the graph model of Exercise 5.14: the sequence tag with its empty-list and cons equations, the set of entries of a list and membership in that set, the application of a coded function, the graph of a map, and the approximability predicate.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise513
public import Mathlib.Data.List.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.entries
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Fun
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.Graph
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.IsApprox
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_nil
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.tag_cons
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514.mem_entries

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


/-! ### The maps `fun` and `graph` -/


end DomainTheory.NeighbourhoodSystems.Exercise514
