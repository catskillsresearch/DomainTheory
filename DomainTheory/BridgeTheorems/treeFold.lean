/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

/-- Canonical section of `treeUnfold`. Product bottom folds to `pairL bot`. -/
def treeFold :
    SumToken α (ProdToken (treeSystem A) (treeSystem A)) → TreeToken α
  | .bot => .bot
  | .left x => .atom x
  | .right p =>
      if p.val.2 = treeBot then .pairL p.val.1 else .pairR p.val.2

end DomainTheory.BridgeTheorems
