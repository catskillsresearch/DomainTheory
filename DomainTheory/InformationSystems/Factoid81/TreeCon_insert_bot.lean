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
public import DomainTheory.InformationSystems.Factoid81.atomFinset_insert_bot
public import DomainTheory.InformationSystems.Factoid81.pairLFinset_insert_bot
public import DomainTheory.InformationSystems.Factoid81.pairRFinset_insert_bot

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

universe u

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem TreeCon_insert_bot {u : Finset (TreeToken α)} (hu : TreeCon A u) :
    TreeCon A (insert .bot u) := by
  cases hu with
  | left _ hA hL hR =>
    exact TreeCon.left _
      (by rw [atomFinset_insert_bot]; exact hA)
      (by rw [pairLFinset_insert_bot]; exact hL)
      (by rw [pairRFinset_insert_bot]; exact hR)
  | right _ hA hL hR =>
    exact TreeCon.right _
      (by rw [atomFinset_insert_bot]; exact hA)
      (by rw [pairLFinset_insert_bot]; exact hL)
      (by rw [pairRFinset_insert_bot]; exact hR)

end InfoSys

end DomainTheory.InformationSystems
