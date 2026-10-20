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
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The consistency test at stage `n+1`: is `enum (n+1)` consistent with the prefix `Y₀,…,Yₙ`?
An `abbrev` so the `[DecidablePred V.mem]` instance is found through it. -/
abbrev cond (n : ℕ) : Prop := V.mem (acc V enum n ∩ enum (n + 1))

end Exercise123

end DomainTheory.NeighbourhoodSystems
