/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.LevelSetPrimrec.lowAnd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- `lowAnd x y = (x &&& y) % 2`. -/
theorem lowAnd_eq_mod (x y : ℕ) : lowAnd x y = (x &&& y) % 2 := by
  have key : ((x &&& y) % 2 = 1) ↔ (x % 2 = 1 ∧ y % 2 = 1) := by
    have hb := Nat.testBit_and x y 0
    rw [Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero] at hb
    rw [← decide_eq_decide, hb, Bool.decide_and]
  unfold lowAnd
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;> rw [hx, hy]
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · have hne : (x &&& y) % 2 ≠ 1 := fun h => by have := key.mp h; omega
    omega
  · exact (key.mpr ⟨hx, hy⟩).symm

end DomainTheory.NeighbourhoodSystems
