/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Exercise 1.14 (Scott 1981, PRG-19, §1) — finite non-empty subsets of `ℕ`

Let `Δ = ℕ` and take as neighbourhoods the **finite non-empty** subsets of `ℕ`, together with `Δ`
itself. This is the infinite analogue of Example 1.5 (where `Δ` was finite).

Deliverables:

* `neighborhoodSystem : NeighborhoodSystem ℕ` — "Show that this is a neighbourhood system." Unlike
  the tail/binary examples this is *not* nested-or-disjoint (two finite sets may overlap partially),
  so condition (ii) is checked by hand: the consistency witness `Z ⊆ X ∩ Y` keeps `X ∩ Y` non-empty,
  and `X ∩ Y` is finite as soon as either factor is.
* **Finite elements.** `fin h = ↑X` (the principal filters), Scott's finite elements.
* **Total elements.** "What are the total elements?" The maximal filters are exactly the principals
  of *singletons*: `singleton_isTotal` shows `↑{n}` is total (a filter strictly above it would have
  to contain a set missing `n`, forcing `∅ ∈ 𝒟`).

Constructive (`[propext, Quot.sound]`).
-/

namespace DomainTheory.Neighborhood.Exercise114

open DomainTheory.Neighborhood NeighborhoodSystem

/-- Membership: `X` is a neighbourhood iff `X = ℕ` (the master `Δ`) or `X` is finite and non-empty. -/
def mem (X : Set ℕ) : Prop := X = Set.univ ∨ (X.Finite ∧ X.Nonempty)

theorem nonempty_of_mem {X : Set ℕ} (h : mem X) : X.Nonempty := by
  rcases h with rfl | h
  · exact Set.univ_nonempty
  · exact h.2

/-- **Exercise 1.14.** The neighbourhood system of finite non-empty subsets of `ℕ` (plus `Δ = ℕ`). -/
def neighborhoodSystem : NeighborhoodSystem ℕ where
  mem := mem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    have hne : (X ∩ Y).Nonempty := (nonempty_of_mem hZ).mono hZsub
    rcases hX with hX | hX
    · rw [hX, Set.univ_inter]; exact hY
    · rcases hY with hY | hY
      · rw [hY, Set.inter_univ]; exact Or.inr hX
      · exact Or.inr ⟨hX.1.inter_of_left Y, hne⟩
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem ns_mem {X : Set ℕ} : neighborhoodSystem.mem X ↔ mem X := Iff.rfl

/-! ### Finite elements (principals) and total elements (singletons). -/

/-- The finite element `↑X` for a neighbourhood `X` (Scott's finite elements). -/
def fin {X : Set ℕ} (h : neighborhoodSystem.mem X) : neighborhoodSystem.Element :=
  neighborhoodSystem.principal h

/-- `⊥ = ↑Δ = ↑ℕ`, the least element. -/
def bot : neighborhoodSystem.Element := neighborhoodSystem.bot
end DomainTheory.Neighborhood.Exercise114
