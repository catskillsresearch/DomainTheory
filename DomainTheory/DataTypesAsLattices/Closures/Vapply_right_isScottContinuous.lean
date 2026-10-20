/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.Vstep_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.eq_5_14
import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous


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
