/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.Factoid81
public import DomainTheory.BridgeTheorems.treeFold
public import DomainTheory.BridgeTheorems.treeFold_eq_or_pairBots
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.mem_closed_pair_bots

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem saturated_of_closed (x : (treeSystem A).Element) {t : TreeToken α}
    (ht : t ∈ x.carrier) : treeFold A (treeUnfold A t) ∈ x.carrier := by
  rcases treeFold_eq_or_pairBots A t with h | ⟨rfl, hf⟩
  · rwa [h]
  · rw [hf]
    exact (mem_closed_pair_bots A x).2 ht

end DomainTheory.BridgeTheorems
