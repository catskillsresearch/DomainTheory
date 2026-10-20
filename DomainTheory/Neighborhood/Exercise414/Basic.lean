/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Exercise 4.14 (Scott 1981, PRG-19, Lecture IV) — `P A` has a maximum fixed point

*Need a monotone function `f : P A → P A` always have a **maximum** fixed point?*

**Yes.** Contrast this with Exercise 4.12, where a general domain `𝒟` admits monotone (indeed
approximable) maps `f : 𝒟 → 𝒟` with no greatest fixed point. The reason is that `P A` — the
power-set domain, whose elements are *arbitrary* subsets of `A` ordered by inclusion — is a
**complete lattice**: arbitrary unions and intersections exist. So both halves of the
Knaster–Tarski theorem apply.

* **Greatest fixed point** (this exercise): `gfpSet f = ⋃ {x ∣ x ⊆ f(x)}` (the union of the
  *post*-fixed points) is a fixed point and dominates every fixed point (`gfpSet_isFixed`,
  `gfpSet_greatest`).
* **Least fixed point** (Exercise 4.13(2), the dual): `lfpSet f = ⋂ {x ∣ f(x) ⊆ x}` (the
  intersection of the *pre*-fixed points) is a fixed point and is dominated by every fixed point
  (`lfpSet_isFixed`, `lfpSet_least`). This is exactly Scott's remark 4.13(2) that the intersection
  construction "can always be applied to power-set domains `P A`" — here `a = A` is the automatic
  pre-fixed point `f(A) ⊆ A`.

Both constructions use **only monotonicity** and the complete-lattice structure of `P A`; they are
entirely **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.Neighborhood.Exercise414

variable {A : Type*}

/-! ### Greatest fixed point — the answer to Exercise 4.14. -/

/-- **Exercise 4.14 (Scott 1981, PRG-19).** The *greatest* fixed point of a monotone `f : P A → P A`,
constructed as the union of all post-fixed points `⋃ {x ∣ x ⊆ f(x)}`. -/
def gfpSet (f : Set A → Set A) : Set A := {a | ∃ x : Set A, x ⊆ f x ∧ a ∈ x}

/-! ### Least fixed point — the dual, realizing Exercise 4.13(2) on `P A`. -/

/-- **Exercise 4.13(2) (Scott 1981, PRG-19).** The *least* fixed point of a monotone `f : P A → P A`,
as the intersection of all pre-fixed points `⋂ {x ∣ f(x) ⊆ x}`. -/
def lfpSet (f : Set A → Set A) : Set A := {a | ∀ x : Set A, f x ⊆ x → a ∈ x}
end DomainTheory.Neighborhood.Exercise414
