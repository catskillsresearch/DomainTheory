/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.interC_app_graph
public import DomainTheory.DataTypesAsLattices.Lambda.interC_then_else_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





































theorem interC_app (x y : Pomega) :
    funOf (funOf interC x) y =
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf interC (predSet x)) (predSet y))) := by
  rw [interC_app_graph]
  exact beta (interC_then_else_isScottContinuous x) y

end DomainTheory.DataTypesAsLattices
