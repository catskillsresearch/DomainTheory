/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.squareFst_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.squareSnd_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.squarePair_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Closures.squarePair_isScottContinuous_right


namespace DomainTheory.DataTypesAsLattices































theorem boxTensor_app (a b u : Pomega) :
    funOf (boxTensor a b) u =
      squarePair (funOf a (squareFst u)) (funOf b (squareSnd u)) :=
  beta (theorem_1_3_tuple
    (f := fun x y => squarePair (funOf a x) (funOf b y))
    (fun y => theorem_1_3 (f := fun x => squarePair x (funOf b y)) (g := funOf a)
      (squarePair_isScottContinuous_left (funOf b y))
      (funOf_isScottContinuous a))
    (fun x => theorem_1_3 (f := fun y => squarePair (funOf a x) y) (g := funOf b)
      (squarePair_isScottContinuous_right (funOf a x))
      (funOf_isScottContinuous b))
    squareFst_isScottContinuous squareSnd_isScottContinuous) u

end DomainTheory.DataTypesAsLattices
