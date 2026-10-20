/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.singletonE_mem
import DomainTheory.DataTypesAsLattices.Functionality.theorem_7_1
import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
import DomainTheory.DataTypesAsLattices.Functionality.Icomb_isGraph


namespace DomainTheory.DataTypesAsLattices






















theorem theorem_7_3_I_unique (i : Pomega)
    (hi : ∀ A, (arrowE A A).mem i) : i = Icomb := by
  have hgraph : i = graph (fun x => funOf i x) := (hi emptyE).1
  apply graph_funOf_ext hgraph Icomb_isGraph
  intro a
  have ha : (singletonE a).mem (funOf i a) :=
    (theorem_7_1 (singletonE a) (singletonE a)).2.1 (hi (singletonE a))
      ((singletonE_mem a a).mpr rfl)
  simpa [Icomb_app, singletonE_mem] using ha

end DomainTheory.DataTypesAsLattices
