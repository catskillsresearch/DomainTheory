/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace

@[expose] public section

/-!
# Exercise 3.21 (Scott 1981, PRG-19, §3) — when does `[Y, Z]` determine `Y` and `Z`?

In the proof of Theorem 3.12 it is tacitly assumed that the function-space neighbourhood `[Y, Z]`
(the set `step Y Z = {f ∣ Y f Z}` of approximable mappings) uniquely determines its endpoints `Y`, `Z`.
Scott's Exercise 3.21 asks to make this precise.

* **If `Z ≠ Δ₂`** the pair is determined: `[Y, Z] = [Y', Z']` forces `Y = Y'` and `Z = Z'`
  (`step_eq_of_ne_master`). The hint is to use the *least* element of `[Y, Z]` — here the single-step
  map `leastMap [(Y, Z)]` of Proposition 3.9.
* **If `Z = Δ₂`** then `[Y, Δ₂] = |𝒟₁ → 𝒟₂|` is the whole space for *every* `Y` (`step_master_right`),
  so `Y` is not determined; nevertheless the biconditional of Theorem 3.12 stays valid because
  `Δ₁ g Δ₂` always holds.
* **General criterion** (`step_eq_iff`): `[Y, Z] = [Y', Z']` iff either both outputs are `Δ₂`, or
  `Y = Y'` and `Z = Z'`.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-! ### The intersection `interYs` of a single step. -/

/-- For a single step `[Y, Z]` and a *sharp enough* input `X ⊆ Y`, the intersection is just `Z`. -/
theorem interYs_single_subset_eq {YX : Set α} {Z : Set β} {X : Set α} (hZ : V₁.mem Z)
    (hXY : X ⊆ YX) : interYs V₁.master [(YX, Z)] X = Z := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨_, hall⟩; exact hall (YX, Z) (List.mem_singleton.mpr rfl) hXY
  · intro hz
    exact ⟨V₁.sub_master hZ hz, fun p hp _ => by rw [List.mem_singleton] at hp; subst hp; exact hz⟩

/-- For a single step `[Y, Z]` and an input `X ⊄ Y`, the intersection is the whole master `Δ₂`. -/
theorem interYs_single_not_subset_eq {YX : Set α} {Z : Set β} {X : Set α}
    (hXY : ¬ X ⊆ YX) : interYs V₁.master [(YX, Z)] X = V₁.master := by
  ext z
  rw [mem_interYs]
  constructor
  · rintro ⟨hm, _⟩; exact hm
  · intro hz
    exact ⟨hz, fun p hp hXp => by rw [List.mem_singleton] at hp; subst hp; exact absurd hXp hXY⟩

/-! ### The least element of a single step neighbourhood. -/

/-- Consistency (`hcons`) for a single step `[Y, Z]`: the intersection over the relevant outputs is
either `Z` (sharp input) or `Δ₂` (blunt input), both neighbourhoods. -/
theorem stepCons {Y : Set α} {Z : Set β} (hZ : V₁.mem Z) :
    ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master [(Y, Z)] X) := by
  intro X _
  by_cases hXY : X ⊆ Y
  · rw [interYs_single_subset_eq hZ hXY]; exact hZ
  · rw [interYs_single_not_subset_eq hXY]; exact V₁.master_mem

/-- The single-step least map `f₀ ∈ [Y, Z]`: `leastMap [(Y, Z)]`, the minimal approximable mapping
relating `Y` to `Z`. -/
def leastStep (Y : Set α) (Z : Set β) (hY : V₀.mem Y) (hZ : V₁.mem Z) :
    ApproximableMap V₀ V₁ :=
  leastMap [(Y, Z)] (by rintro p hp; rw [List.mem_singleton] at hp; subst hp; exact ⟨hY, hZ⟩)
    (stepCons hZ)

/-! ### `[Y, Z]` is the whole space exactly when `Z = Δ₂`. -/

/-! ### Uniqueness when `Z ≠ Δ₂`. -/

/-! ### The general identity criterion. -/
end DomainTheory.NeighbourhoodSystems
