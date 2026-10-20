/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Definition 7.9 — the Smyth power domain `ℙ𝒟`.** A set `W : Set (Set α)` is a
neighbourhood of `ℙ𝒟` iff it is a *finite union of down-sets* `⋃_{X ∈ L} ↓X` for some finite
list `L` of `𝒟`-neighbourhoods. The empty list `L = []` realizes Scott's `n = 0` (the empty
union `∅`). -/
def PDmem (W : Set (Set α)) : Prop :=
  ∃ L : List (Set α), (∀ X ∈ L, V.mem X) ∧ W = ⋃ X ∈ L, V.upSet X

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
