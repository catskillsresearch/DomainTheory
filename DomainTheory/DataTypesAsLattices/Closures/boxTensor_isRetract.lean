/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.eq_5_9
import DomainTheory.DataTypesAsLattices.Closures.eq_5_10
import DomainTheory.DataTypesAsLattices.Closures.boxTensor_app


namespace DomainTheory.DataTypesAsLattices































theorem boxTensor_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (boxTensor a b) := by
  change boxTensor a b =
    graph (fun u => funOf (boxTensor a b) (funOf (boxTensor a b) u))
  apply graph_ext
  intro u
  rw [boxTensor_app, boxTensor_app, eq_5_9, eq_5_10, retract_app ha, retract_app hb]

end DomainTheory.DataTypesAsLattices
