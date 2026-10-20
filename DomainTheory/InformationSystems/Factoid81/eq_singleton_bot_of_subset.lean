/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Product
public import DomainTheory.InformationSystems.Sum
public import DomainTheory.InformationSystems.Factoid81.TreeToken
public import DomainTheory.InformationSystems.Factoid81.TreeCon
public import DomainTheory.InformationSystems.Factoid81.TreeCon
public import DomainTheory.InformationSystems.Factoid81.atomFinset
public import DomainTheory.InformationSystems.Factoid81.pairLFinset
public import DomainTheory.InformationSystems.Factoid81.pairRFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem eq_singleton_bot_of_subset {s : Finset (TreeToken α)}
    (hne : s ≠ ∅) (hsub : s ⊆ {.bot}) : s = {.bot} := by
  ext y
  constructor
  · exact fun hy => hsub hy
  · intro hy
    have : y = .bot := Finset.mem_singleton.1 hy
    subst this
    obtain ⟨z, hz⟩ := Finset.nonempty_of_ne_empty hne
    have hzbot : z = .bot := Finset.mem_singleton.1 (hsub hz)
    exact hzbot ▸ hz

end InfoSys

end DomainTheory.InformationSystems
