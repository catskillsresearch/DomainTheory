/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boxShift_map_isScottContinuous


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_app (a x : Pomega) :
    funOf (boxShift a) x = ofNat 0 ∪ succSet (funOf a (predSet x)) :=
  beta (boxShift_map_isScottContinuous a) x

end DomainTheory.DataTypesAsLattices
