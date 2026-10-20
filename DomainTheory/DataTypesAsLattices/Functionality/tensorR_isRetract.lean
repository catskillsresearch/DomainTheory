/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, Theorem 4.4.** Products of retracts are retracts. -/
theorem tensorR_isRetract {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    IsRetract (tensorR a b) := by
  change tensorR a b =
    graph (fun u => funOf (tensorR a b) (funOf (tensorR a b) u))
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one,
    retract_app ha, retract_app hb]

end DomainTheory.DataTypesAsLattices
