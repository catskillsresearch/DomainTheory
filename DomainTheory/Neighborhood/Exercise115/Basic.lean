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
# Exercise 1.15 (Scott 1981, PRG-19, §1) — non-isomorphic "finite-only" domains

"Construct non-isomorphic infinite domains where all elements are finite but where there are no
infinite chains `⟨xₙ⟩` of elements with `xₙ ⊏ xₙ₊₁` for all `n`."

We give two neighbourhood systems over `Δ = ℕ`:

* **`flat`** — `𝒟 = {ℕ} ∪ {{n} ∣ n ∈ ℕ}` (the *flat* domain). Its elements are exactly `⊥` and the
  pairwise-incomparable atoms `↑{n}` (`flat_classify`), so **all elements are finite/principal**
  (`flat_all_finite`), every atom is **maximal** (`flat_atom_maximal`), there is **no 3-chain**
  (`flat_no_three_chain`) and hence **no infinite ascending chain** (`flat_no_infinite_chain`). It is
  infinite (`flat_infinite`).

* **`stem`** — `𝒟 = {ℕ, {0,1}} ∪ {{n} ∣ n ∈ ℕ}` (a flat domain with one length-3 "stem"). It
  contains a strict **3-chain** `⊥ ⊏ ↑{0,1} ⊏ ↑{0}` (`stem_three_chain`). It too has only finite
  elements and no infinite ascending chain (same flat-with-stem classification; the formally decisive
  difference from `flat` is the 3-chain).

Since an order-isomorphism transports strict chains, the 3-chain in `stem` would force a 3-chain in
`flat`, which has none: hence `¬ (flat ≅ᴰ stem)` (`not_isomorphic`). Two infinite, finite-element,
chain-bounded domains that are *not* isomorphic.

The classification results are *classical* (they decide whether an element contains some atom); the
constructions and the non-isomorphism argument are otherwise elementary.
-/

namespace DomainTheory.Neighborhood.Exercise115

open DomainTheory.Neighborhood NeighborhoodSystem

/-- `{n} ∩ {m} = ∅` for `n ≠ m`. -/
theorem singleton_disjoint {n m : ℕ} (h : n ≠ m) : ({n} : Set ℕ) ∩ {m} = ∅ := by
  ext k
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl, h2⟩
  exact h h2

/-! ## The flat domain `flat`. -/

/-- Neighbourhoods of the flat domain: `Δ = ℕ` together with all singletons. -/
def flatMem (X : Set ℕ) : Prop := X = Set.univ ∨ ∃ n, X = {n}

theorem flatNOD : NestedOrDisjoint flatMem := by
  rintro X Y (rfl | ⟨n, rfl⟩) (rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

/-- **Exercise 1.15 — the flat domain.** `𝒟 = {ℕ} ∪ {{n}}`. -/
def flat : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint flatMem Set.univ Set.univ_nonempty
    (Or.inl rfl) flatNOD (fun _ => Set.subset_univ _)

@[simp] theorem flat_mem {X : Set ℕ} : flat.mem X ↔ X = Set.univ ∨ ∃ n, X = {n} := Iff.rfl

@[simp] theorem flat_master : flat.master = Set.univ := rfl

/-! ## The "stem" domain `stem`. -/

/-- Neighbourhoods of the stem domain: `Δ = ℕ`, the pair `{0,1}`, and all singletons. -/
def stemMem (X : Set ℕ) : Prop := X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n}

theorem stemNOD : NestedOrDisjoint stemMem := by
  have pair_single : ∀ m : ℕ, ({m} : Set ℕ) ⊆ {0, 1} ∨ ({0, 1} : Set ℕ) ∩ {m} = ∅ := by
    intro m
    by_cases h : m = 0 ∨ m = 1
    · refine Or.inl ?_
      rcases h with rfl | rfl <;> intro k hk <;> simp_all
    · refine Or.inr ?_
      ext k
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      rintro (rfl | rfl) rfl <;> simp_all
  rintro X Y (rfl | rfl | ⟨n, rfl⟩) (rfl | rfl | ⟨m, rfl⟩)
  · exact Or.inl (subset_refl _)
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inr (Or.inl (Set.subset_univ _))
  · exact Or.inl (Set.subset_univ _)
  · exact Or.inl (subset_refl _)
  · rcases pair_single m with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (Set.subset_univ _)
  · rcases pair_single n with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by rw [Set.inter_comm]; exact h))
  · rcases eq_or_ne n m with rfl | h
    · exact Or.inl (subset_refl _)
    · exact Or.inr (Or.inr (singleton_disjoint h))

/-- **Exercise 1.15 — the stem domain.** `𝒟 = {ℕ, {0,1}} ∪ {{n}}`. -/
def stem : NeighborhoodSystem ℕ :=
  ofNestedOrDisjoint stemMem Set.univ Set.univ_nonempty
    (Or.inl rfl) stemNOD (fun _ => Set.subset_univ _)

@[simp] theorem stem_mem {X : Set ℕ} :
    stem.mem X ↔ X = Set.univ ∨ X = {0, 1} ∨ ∃ n, X = {n} := Iff.rfl

/-! ## Non-isomorphism. -/
end DomainTheory.Neighborhood.Exercise115
