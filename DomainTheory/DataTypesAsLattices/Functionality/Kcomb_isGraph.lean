/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.Kcomb_app


namespace DomainTheory.DataTypesAsLattices






















theorem Kcomb_isGraph : Kcomb = graph (fun x => funOf Kcomb x) := by
  apply graph_ext
  intro x
  rw [Kcomb_app]

end DomainTheory.DataTypesAsLattices
