/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- Exercise 1.20's `↑X = {Y ∈ 𝒟 ∣ Y ⊆ X}` (the up-set of `X` *inside* `𝒟`). -/
def upSet (X : Set α) : Set (Set α) := {Y | V.mem Y ∧ Y ⊆ X}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
