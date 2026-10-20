/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.predSet_union
import DomainTheory.DataTypesAsLattices.Closures.predSet_succSet
import DomainTheory.DataTypesAsLattices.Closures.boxShift_app


namespace DomainTheory.DataTypesAsLattices































theorem boxShift_isRetract {a : Pomega} (ha : IsRetract a) :
    IsRetract (boxShift a) := by
  change boxShift a =
    graph (fun x => funOf (boxShift a) (funOf (boxShift a) x))
  apply graph_ext
  intro x
  rw [boxShift_app, boxShift_app]
  have hpred : predSet (ofNat 0 ∪ succSet (funOf a (predSet x))) =
      funOf a (predSet x) := by
    rw [predSet_union, predSet_ofNat_zero, predSet_succSet]
    simp [botElem]
  rw [hpred, retract_app ha]

end DomainTheory.DataTypesAsLattices
