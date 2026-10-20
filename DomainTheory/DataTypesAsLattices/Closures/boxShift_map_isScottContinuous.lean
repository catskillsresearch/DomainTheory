/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.union_const_left_isScottContinuous


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_map_isScottContinuous (a : Pomega) :
    IsScottContinuous (fun x => ofNat 0 ∪ succSet (funOf a (predSet x))) :=
  theorem_1_3 (union_const_left_isScottContinuous (ofNat 0))
    (theorem_1_3 succSet_isScottContinuous
      (theorem_1_3 (funOf_isScottContinuous a) predSet_isScottContinuous))

end DomainTheory.DataTypesAsLattices
