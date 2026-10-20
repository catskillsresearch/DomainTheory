/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Embedding
public import DomainTheory.DataTypesAsLattices.Lambda.Basic
public import DomainTheory.DataTypesAsLattices.Lambda.succSet_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Lambda.condSet_isScottContinuous_right
public import DomainTheory.DataTypesAsLattices.Lambda.funOf_isScottContinuous_left
public import DomainTheory.DataTypesAsLattices.Lambda.graph_const_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices




































theorem interStep_isScottContinuous :
    IsScottContinuous interStep := by
  refine graph_const_isScottContinuous
    (fun f x => graph (fun y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y))))) ?_
  intro x
  refine graph_const_isScottContinuous
    (fun f y =>
      condSet x (condSet y (ofNat 0) botElem)
        (succSet (funOf (funOf f (predSet x)) (predSet y)))) ?_
  intro y
  refine theorem_1_3
    (condSet_isScottContinuous_right x (condSet y (ofNat 0) botElem)) ?_
  refine theorem_1_3 succSet_isScottContinuous ?_
  exact theorem_1_3
    (f := fun t => funOf t (predSet y))
    (g := fun f => funOf f (predSet x))
    (funOf_isScottContinuous_left (predSet y))
    (funOf_isScottContinuous_left (predSet x))

end DomainTheory.DataTypesAsLattices
