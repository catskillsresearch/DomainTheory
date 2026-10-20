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

def genAtom {β : Type*} (Z : ℕ → Set β) (M : Set β) (δ : ℕ → Bool) : ℕ → Set β
  | 0 => M
  | (n + 1) => genAtom Z M δ n ∩ (if δ n then Z n else M \ Z n)

end DomainTheory.NeighbourhoodSystems
