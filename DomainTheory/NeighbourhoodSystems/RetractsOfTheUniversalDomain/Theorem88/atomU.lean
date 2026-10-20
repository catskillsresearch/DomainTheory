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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88.genAtom

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

variable {α : Type*}

variable (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)

/-- The `U`-side atom matching `genAtom X Δ δ n`, built recursively via an abstract splitting
operation `split` (instantiated with `splitChoice` for Theorem 8.8(a), `splitEff` for 8.8(b)). -/
noncomputable def atomU (split : Set α → Set ℚ → Set α → Set ℚ × Set ℚ)
    (X : ℕ → Set α) (Δ : Set α) (δ : ℕ → Bool) : ℕ → Set ℚ
  | 0 => U.master
  | (n + 1) =>
      if δ n then (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).1
      else (split (genAtom X Δ δ n) (atomU split X Δ δ n) (X n)).2

end DomainTheory.NeighbourhoodSystems
