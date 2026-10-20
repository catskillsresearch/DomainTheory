/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.curry_mid_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Functionality.curryC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem curryC_app2 (u x : Pomega) :
    funOf (funOf curryC u) x = graph (fun y => funOf u (pairSeq x y)) := by
  rw [curryC_app]
  exact beta (curry_mid_isScottContinuous u) x

end DomainTheory.DataTypesAsLattices
