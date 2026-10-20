/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.funRetract_app
import DomainTheory.DataTypesAsLattices.Retracts.graph_ext


namespace DomainTheory.DataTypesAsLattices






































theorem funRetract_isRetract : IsRetract funRetract := by
  apply graph_ext
  intro u
  rw [funRetract_app, funRetract_app]
  apply graph_ext
  intro x
  exact (beta (funOf_isScottContinuous u) x).symm

end DomainTheory.DataTypesAsLattices
