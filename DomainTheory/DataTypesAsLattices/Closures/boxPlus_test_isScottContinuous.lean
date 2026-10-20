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
import DomainTheory.DataTypesAsLattices.Closures.union_left_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.union_const_left_isScottContinuous
import DomainTheory.DataTypesAsLattices.Closures.boxTag_isScottContinuous


namespace DomainTheory.DataTypesAsLattices































theorem boxPlus_test_isScottContinuous :
    IsScottContinuous (fun u => boxTag 0 (squareFst u) ∪ boxTag 1 (squareSnd u)) :=
  theorem_1_3_tuple
    (fun y => union_left_isScottContinuous y)
    (fun x => union_const_left_isScottContinuous x)
    (theorem_1_3 (boxTag_isScottContinuous 0) squareFst_isScottContinuous)
    (theorem_1_3 (boxTag_isScottContinuous 1) squareSnd_isScottContinuous)

end DomainTheory.DataTypesAsLattices
