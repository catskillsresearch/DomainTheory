/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise118
import Mathlib.Tactic

/-!
# Exercise 1.27 (Scott 1981, PRG-19, §1) — bounded sets and least upper bounds

Scott introduces *bounded* sets of elements as the analogue, for `|𝒟|`, of *consistent*
sequences of neighbourhoods. A set `X ⊆ |𝒟|` is **bounded** iff it has an upper bound
`y ∈ |𝒟|` (`x ⊑ y` for all `x ∈ X`), and then

`⊔X = ⋂ {y ∣ x ⊑ y for all x ∈ X}`

is its **least upper bound**. This file formalizes:

* `Bounded X` and `sSup X hX := sInf (upper bounds of X)` — the upper-bound family is non-empty
  exactly because `X` is bounded, so we reuse `sInf` from Exercise 1.18; the lub laws
  `le_sSup` / `sSup_le` are then immediate from `le_sInf` / `sInf_le`;
* `consistent_pair_iff_bounded` — for `U, W ∈ 𝒟`, the pair `⟨U, W⟩` is `Consistent` iff
  `{↑U, ↑W}` is bounded ("boundedness is for elements what consistency is for neighbourhoods");
* `bounded_iff_finite_bounded` — **with the aid of Exercise 1.18**, `X` is bounded iff every
  *finite* subset of `X` is bounded; the hard direction builds the bound as the `leastFilter`
  of `C = ⋃_{x∈X} x`, whose finite consistency comes from the finite bounds.

The constructions (`sSup`) are `[propext, Quot.sound]`. The hard direction of
`bounded_iff_finite_bounded` selects a finite witness set via `Classical.choice`; this is a
*proof*, so the construction stays choice-free.
-/

namespace DomainTheory.Neighborhood

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Exercise 1.27 — bounded set of elements.** `X ⊆ |𝒟|` is *bounded* iff it has an upper
bound `y ∈ |𝒟|`: `x ⊑ y` for all `x ∈ X`. -/
def Bounded (X : Set V.Element) : Prop := ∃ y : V.Element, ∀ x ∈ X, x ≤ y

/-- The family of upper bounds of `X`: `{y ∣ x ⊑ y for all x ∈ X}`. -/
def upperBounds (X : Set V.Element) : Set V.Element := {y | ∀ x ∈ X, x ≤ y}

/-- If `X` is bounded then its upper-bound family is non-empty (it contains the witness). -/
theorem upperBounds_nonempty {X : Set V.Element} (hX : V.Bounded X) :
    (V.upperBounds X).Nonempty :=
  hX.imp fun _ hy => hy

/-- **Exercise 1.27 — `⊔X`.** The least upper bound of a bounded `X`, defined à la Scott as the
intersection of all upper bounds: `⊔X = ⋂ {y ∣ x ⊑ y all x∈X}`. Reusing `sInf` from Exercise
1.18 on the (non-empty, because bounded) family of upper bounds. -/
def sSup (X : Set V.Element) (hX : V.Bounded X) : V.Element :=
  V.sInf (V.upperBounds X) (V.upperBounds_nonempty hX)

/-! ### Boundedness of `{↑U, ↑W}` ⟺ consistency of `⟨U, W⟩`. -/

/-- The two-term sequence `⟨U, W⟩` as a function `ℕ → Set α` (used to phrase `Consistent`). -/
def pairSeq (U W : Set α) : ℕ → Set α := fun i => if i = 0 then U else W

/-! ### Boundedness is finitary (with the aid of Exercise 1.18). -/
end NeighborhoodSystem
end DomainTheory.Neighborhood
