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









































theorem typed_arrowR_restrict {a b u : Pomega}
    (ha : IsRetract a) (hu : typed u (arrowR a b)) :
    u = comp u a := by
  have hu' := typed_of_arrowR hu
  have h : comp (comp b (comp u a)) a = comp b (comp u a) := by
    apply graph_ext
    intro x
    simp only [comp_app]
    rw [retract_app ha]
  have : comp u a = comp (comp b (comp u a)) a := by
    conv_lhs => rw [hu']
  exact ((this.trans h).trans hu'.symm).symm

end DomainTheory.DataTypesAsLattices
