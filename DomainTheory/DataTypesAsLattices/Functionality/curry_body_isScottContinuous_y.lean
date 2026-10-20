/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















theorem curry_body_isScottContinuous_y (u x : Pomega) :
    IsScottContinuous (fun y => funOf u (pairSeq x y)) :=
  theorem_1_3 (funOf_isScottContinuous u) (pairSeq_isScottContinuous_right x)

end DomainTheory.DataTypesAsLattices
