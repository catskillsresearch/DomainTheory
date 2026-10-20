/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.union_right_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.Vstep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_14

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem Vapply_left_isScottContinuous (x : Pomega) :
    IsScottContinuous (fun a => Vapply a x) := by
  have : (fun a => Vapply a x) = (fun a => VapplyY a x) := by
    funext a; exact (eq_5_14 a x).symm
  rw [this]
  exact fix_param_isScottContinuous
    (fun y => union_right_isScottContinuous x (funOf_isScottContinuous_left y))
    (fun a => Vstep_isScottContinuous a x)

end DomainTheory.DataTypesAsLattices
