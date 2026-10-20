/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app
import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_app


namespace DomainTheory.DataTypesAsLattices































/-- **Scott 1976, Theorem 5.4 (sum half), idempotence.** -/
theorem boxPlus_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (boxPlus a b) := by
  change boxPlus a b =
    graph (fun u => funOf (boxPlus a b) (funOf (boxPlus a b) u))
  apply graph_ext
  intro u
  rw [boxPlus_app_app ha hb u, boxPlus_app]

end DomainTheory.DataTypesAsLattices
