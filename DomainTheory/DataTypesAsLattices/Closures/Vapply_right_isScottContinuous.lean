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
public import DomainTheory.DataTypesAsLattices.Closures.Vstep_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.eq_5_14
public import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem Vapply_right_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => Vapply a x) := by
  have : (fun x => Vapply a x) = (fun x => VapplyY a x) := by
    funext x; exact (eq_5_14 a x).symm
  rw [this]
  exact fix_param_isScottContinuous
    (fun y => union_left_isScottContinuous (funOf a y))
    (fun x => Vstep_isScottContinuous a x)

end DomainTheory.DataTypesAsLattices
