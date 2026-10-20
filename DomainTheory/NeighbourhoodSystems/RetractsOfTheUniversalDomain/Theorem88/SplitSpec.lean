/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87
public import Mathlib.Data.Fintype.Pi
import all Mathlib.Data.Fintype.Pi

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

/-- **The abstract specification a splitting operation must satisfy** — exactly `exists_split`'s
conclusion, as a `Prop` about a *total* function `split`. Both the classical `splitChoice` (via
`Classical.choice`) and the effective, computable `splitEff` (Theorem 8.8(b)) satisfy this. -/
def SplitSpec (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ) : Prop :=
  ∀ {A : Set α} {B : Set ℚ}, (A = ∅ ↔ B = ∅) → (B = ∅ ∨ U.mem B) → ∀ Xn : Set α,
    ((split A B Xn).1 = ∅ ∨ U.mem (split A B Xn).1) ∧
      ((split A B Xn).2 = ∅ ∨ U.mem (split A B Xn).2) ∧
      (A ∩ Xn = ∅ ↔ (split A B Xn).1 = ∅) ∧
      (A \ Xn = ∅ ↔ (split A B Xn).2 = ∅) ∧
      (split A B Xn).1 ∪ (split A B Xn).2 = B ∧
      (split A B Xn).1 ∩ (split A B Xn).2 = ∅

end DomainTheory.NeighbourhoodSystems
