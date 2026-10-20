/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic


namespace DomainTheory.DataTypesAsLattices






















theorem Icomb_isGraph : Icomb = graph (fun x => funOf Icomb x) := by
  apply graph_ext
  intro x
  rw [Icomb_app]

end DomainTheory.DataTypesAsLattices
