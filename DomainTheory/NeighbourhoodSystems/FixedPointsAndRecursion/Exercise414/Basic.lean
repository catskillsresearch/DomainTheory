/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Data.Set.Basic
import all Mathlib.Data.Set.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.gfpSet
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet

@[expose] public section

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

namespace DomainTheory.NeighbourhoodSystems.Exercise414

variable {A : Type*}

/-! ### Greatest fixed point — the answer to Exercise 4.14. -/


/-! ### Least fixed point — the dual, realizing Exercise 4.13(2) on `P A`. -/

end DomainTheory.NeighbourhoodSystems.Exercise414
