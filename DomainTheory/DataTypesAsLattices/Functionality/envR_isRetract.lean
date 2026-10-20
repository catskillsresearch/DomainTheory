/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.lambR_isRetract
import DomainTheory.DataTypesAsLattices.Functionality.envR_app


namespace DomainTheory.DataTypesAsLattices

































theorem envR_isRetract : IsRetract envR := by
  change envR = graph (fun t => funOf envR (funOf envR t))
  apply graph_ext
  intro t
  rw [envR_app, envR_app]
  apply graph_ext
  intro n
  have hβ : funOf (graph (fun m => funOf lambR (funOf t m))) n =
      funOf lambR (funOf t n) :=
    beta (theorem_1_3 (funOf_isScottContinuous lambR)
      (funOf_isScottContinuous t)) n
  rw [hβ, retract_app lambR_isRetract]

end DomainTheory.DataTypesAsLattices
