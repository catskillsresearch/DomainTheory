/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.FixedLattices
import DomainTheory.DataTypesAsLattices.Lambda
import DomainTheory.DataTypesAsLattices.Retracts.Basic
import DomainTheory.DataTypesAsLattices.Retracts.graph_ext
import DomainTheory.DataTypesAsLattices.Retracts.typed_of_arrowR


namespace DomainTheory.DataTypesAsLattices









































theorem typed_arrowR_range {a b u : Pomega}
    (hb : IsRetract b) (hu : typed u (arrowR a b)) :
    u = comp b u := by
  have hu' := typed_of_arrowR hu
  rw [hu']
  apply graph_ext
  intro x
  simp only [comp_app]
  rw [retract_app hb]

end DomainTheory.DataTypesAsLattices
