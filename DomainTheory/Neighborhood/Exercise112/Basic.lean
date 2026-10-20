/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.Neighborhood.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

/-!
# Exercise 1.12 (Scott 1981, PRG-19, §1) — the final-segment system on `ℕ`

Let `Δ = ℕ` and take as neighbourhoods the **final segments** (tails)

`tail n = {m ∈ ℕ ∣ n ≤ m}`,

so `tail 0 = ℕ = Δ` and `tail 0 ⊇ tail 1 ⊇ tail 2 ⊇ ⋯` is a descending chain (Scott's `{m ∣ m > n}`
is `tail (n+1)`). This generalizes Example 1.3 (a *chain*) to the countably infinite case.

Deliverables:

* `neighborhoodSystem : NeighborhoodSystem ℕ` (the tails are pairwise nested, so Factoid 1.4a
  applies) — verifies it is a neighbourhood system.
* **Finite elements.** `fin n = ↑(tail n)`, the principal filters; they form an ascending `ω`-chain
  `fin 0 ⊏ fin 1 ⊏ ⋯` (`fin_le_iff`, `fin_strictMono`).
* **The limit / total element.** `top = 𝒟` itself (all tails) is the greatest element (`le_top`),
  is the *unique* total (maximal) element (`top_isTotal`, `isTotal_iff_top`).
* **Classification** (the "only one limit element" hint): every element is either a finite `fin n`
  or the limit `top` (`element_eq`). This single result is *classical* (it decides whether the set
  of indices in `x` is bounded — `Nat.find` over a `¬`-predicate); everything else is constructive.
-/

namespace DomainTheory.Neighborhood.Exercise112

open DomainTheory.Neighborhood NeighborhoodSystem

/-- The final segment (tail) `tail n = {m ∣ n ≤ m}`; the neighbourhood "all integers `≥ n`". -/
def tail (n : ℕ) : Set ℕ := {m | n ≤ m}

@[simp] theorem mem_tail {n m : ℕ} : m ∈ tail n ↔ n ≤ m := Iff.rfl

/-- A longer tail is a *smaller* set: `tail n ⊆ tail m ↔ m ≤ n`. -/
theorem tail_subset_iff {n m : ℕ} : tail n ⊆ tail m ↔ m ≤ n := by
  constructor
  · intro h
    exact h (show n ∈ tail n from le_refl n)
  · intro hmn k hk
    exact le_trans hmn hk

/-- `tail n ∩ tail m = tail (max n m)` (the intersection of two tails is the shorter one). -/
theorem tail_inter (n m : ℕ) : tail n ∩ tail m = tail (max n m) := by
  ext k
  simp only [Set.mem_inter_iff, mem_tail]
  omega

/-- Membership in the final-segment system: `X` is a neighbourhood iff `X = tail n` for some `n`. -/
def mem (X : Set ℕ) : Prop := ∃ n, X = tail n

theorem nestedOrDisjoint : NestedOrDisjoint mem := by
  rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
  rcases le_total n m with h | h
  · exact Or.inr (Or.inl (tail_subset_iff.mpr h))
  · exact Or.inl (tail_subset_iff.mpr h)

/-- **Exercise 1.12.** The final-segment neighbourhood system on `ℕ` (master `Δ = tail 0 = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint mem (tail 0) ⟨0, Nat.zero_le 0⟩ ⟨0, rfl⟩ nestedOrDisjoint
    (fun {X} hX => by obtain ⟨n, rfl⟩ := hX; exact tail_subset_iff.mpr (Nat.zero_le n))

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ ∃ n, X = tail n := Iff.rfl

theorem mem_tail_nbhd (n : ℕ) : neighborhoodSystem.mem (tail n) := ⟨n, rfl⟩

/-! ### Finite elements: the principal filters `fin n = ↑(tail n)`. -/

/-- The finite element `fin n = ↑(tail n)` (principal filter of the tail). -/
def fin (n : ℕ) : neighborhoodSystem.Element := neighborhoodSystem.principal (mem_tail_nbhd n)

/-! ### The limit element: the whole system `𝒟`, the greatest / unique total element. -/

/-- The **limit element** `top`: the filter of *all* tails (Scott's single limit node). -/
def top : neighborhoodSystem.Element where
  mem X := neighborhoodSystem.mem X
  sub h := h
  master_mem := neighborhoodSystem.master_mem
  inter_mem := by
    rintro X Y ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨max n m, tail_inter n m⟩
  up_mem _ hY _ := hY

@[simp] theorem mem_top {X : Set ℕ} : top.mem X ↔ neighborhoodSystem.mem X := Iff.rfl

/-! ### Classification: finite `fin n`, or the limit `top` (classical). -/
end DomainTheory.Neighborhood.Exercise112
