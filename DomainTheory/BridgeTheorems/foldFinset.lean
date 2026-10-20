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
public import DomainTheory.BridgeTheorems.SexDomainEquationInst10
public import DomainTheory.BridgeTheorems.foldInsert
public import DomainTheory.BridgeTheorems.SexDomainEquationInst15

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Choice-free image of an RHS finset under `treeFold`. -/
def foldFinset (Y : Finset (SumToken α (ProdToken (treeSystem A) (treeSystem A)))) :
    Finset (TreeToken α) :=
  Multiset.foldr (foldInsert A) ∅ Y.1

end DomainTheory.BridgeTheorems
