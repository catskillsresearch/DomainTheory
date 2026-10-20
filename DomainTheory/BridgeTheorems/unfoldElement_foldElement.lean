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
public import DomainTheory.BridgeTheorems.treeUnfold_treeFold
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15
public import DomainTheory.BridgeTheorems.unfoldElement
public import DomainTheory.BridgeTheorems.foldElement

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem unfoldElement_foldElement (y : (treeRhs A).Element) :
    unfoldElement A (foldElement A y) = y := by
  refine le_antisymm ?_ ?_
  · intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    exact ht
  · intro s hs
    refine ⟨treeFold A s, ?_, treeUnfold_treeFold A s⟩
    change treeUnfold A (treeFold A s) ∈ y.carrier
    rwa [treeUnfold_treeFold]

end DomainTheory.BridgeTheorems
