/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem86
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88

@[expose] public section

/-!
# Exercise 8.16 (Scott 1981, PRG-19)

> **Exercise 8.16.** For finitary projections `a : E → E`, write `D_a = {X ∈ E ∣ X ⊑ aX}` (cf. 8.5).
> Show that for any two such projections `a, b : E → E` we have `a ⊑ b iff D_a ◁ D_b`. (This fills
> in the gap at the end of the proof of 8.6.) Also finish off the proof of 8.8 by showing that if
> `E` is effectively given and `a : E → E` is computable, then `D_a` is effectively given.

## What is formalized here

Both halves turn out to already be (nearly) proved by existing machinery, so this file is a thin
assembly layer:

* **Part 1** (`isFinitaryProjection_le_iff_fixedNbhd_subsystem`): `D_a` is exactly Theorem 8.5's
  `fixedNbhd a`, and `a ≤ b ↔ fixedNbhd a ◁ fixedNbhd b` for finitary `a, b` is exactly Theorem
  8.6(a)'s order-isomorphism `finitaryProjectionSubsystemEquiv` (`{f ∣ sub f = f} ≃o {D ∣ D ◁ E}`,
  where `≤` on the right is *literally* `◁`, `Proposition611.lean`), restricted from `sub`-fixed
  points to finitary projections via `sub_eq_self_iff_isFinitaryProjection`. We avoid depending on
  the exact implicit-argument names of the generated `OrderIso.map_rel_iff` and instead assemble
  both directions directly from `OrderIso.monotone`/`OrderIso.symm.monotone` plus
  `OrderIso.symm_apply_apply`, which is robust to Mathlib's internal naming.
* **Part 2** (`exercise_8_16`'s second conjunct): already proved in full generality as
  `Theorem88m.lean`'s `fixedNbhd_isEffectivelyGiven` — "`a` computable relative to a
  `ComputablePresentation P` of `E`" (`IsComputableMap P P a`) already packages "`E` effectively
  given (via `P`) and `a` computable (relative to `P`)"; no new proof is needed, only restating it
  under this exercise's name.

Everything here is **choice-free** (`⊆ {propext, Quot.sound}`): Part 1 is built purely from order
theory on `finitaryProjectionSubsystemEquiv` (itself choice-free, Theorem 8.6(a)), and Part 2 is a
direct citation of the already-audited choice-free `fixedNbhd_isEffectivelyGiven`.
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}
end DomainTheory.NeighbourhoodSystems
