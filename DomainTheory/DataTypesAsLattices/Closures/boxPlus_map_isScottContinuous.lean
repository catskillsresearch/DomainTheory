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
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_test_isScottContinuous


namespace DomainTheory.DataTypesAsLattices































theorem boxPlus_map_isScottContinuous (a b : Pomega) :
    IsScottContinuous (fun u =>
      dcondSet (boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u))
        (squarePair (funOf (boxShift a) (squareFst u)) botElem)
        (squarePair botElem (funOf (boxShift b) (squareSnd u)))) :=
  theorem_1_3_nary
    (fun y z => dcondSet_isScottContinuous_left y z)
    (fun x z => dcondSet_isScottContinuous_mid x z)
    (fun x y => dcondSet_isScottContinuous_right x y)
    boxPlus_test_isScottContinuous
    (theorem_1_3 (f := fun x => squarePair x botElem)
      (g := fun u => funOf (boxShift a) (squareFst u))
      (squarePair_isScottContinuous_left botElem)
      (theorem_1_3 (funOf_isScottContinuous (boxShift a)) squareFst_isScottContinuous))
    (theorem_1_3 (f := fun y => squarePair botElem y)
      (g := fun u => funOf (boxShift b) (squareSnd u))
      (squarePair_isScottContinuous_right botElem)
      (theorem_1_3 (funOf_isScottContinuous (boxShift b)) squareSnd_isScottContinuous))

end DomainTheory.DataTypesAsLattices
