/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Scomb_app


namespace DomainTheory.DataTypesAsLattices






















theorem Scomb_isGraph : Scomb = graph (fun u => funOf Scomb u) := by
  apply graph_ext
  intro u
  rw [Scomb_app]

end DomainTheory.DataTypesAsLattices
