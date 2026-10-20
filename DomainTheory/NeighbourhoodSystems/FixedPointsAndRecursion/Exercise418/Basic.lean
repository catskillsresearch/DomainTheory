/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43

@[expose] public section

/-!
# Exercise 4.18 (Scott 1981, PRG-19, Lecture IV)

*In Example 4.3 there are many unproved assertions about `N` and `F`. These should be checked.*

`Example43.lean` builds the natural-number domain `N`, the total elements `n̂ = natElem n`, and the
structure maps `succ`, `pred`, `zero` with their value equations. This file discharges the remaining
*structural* assertions Scott leaves implicit:

* **Element classification** (`element_classification`): `|N|` consists of exactly `⊥` and the total
  elements `n̂` — `N` is genuinely the *flat* domain over `ℕ`. (This is the assertion that makes `N`
  "THE domain of integers".)
* **Peano's axioms for the total elements** `⟨{n̂}, 0̂, succ⟩`:
  - `natElem_injective` / `succMap_injective`: distinct numerals are distinct elements, and `succ` is
    one-one;
  - `natElem_zero_ne_succ` / `zero_ne_succMap`: `0̂` is not a successor;
  - `predMap_succMap_natElem` (already in `Example43`): `pred ∘ succ = id` on numerals.

The classification is classical (it decides whether `x` contains a singleton, exactly as Example 4.3's
`zeroMap` is classical); the injectivity / zero-is-not-a-successor facts are **choice-free**.
-/

namespace DomainTheory.NeighbourhoodSystems.Exercise418

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap Example43

/-- Distinct singletons are disjoint. -/
theorem singleton_inter_eq_empty {n m : ℕ} (hmn : m ≠ n) :
    ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl h2
  exact hmn h2.symm
end DomainTheory.NeighbourhoodSystems.Exercise418
