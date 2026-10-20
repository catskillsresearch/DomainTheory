/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.union_right_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.Vstep_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.eq_5_14


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
