/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic
import DomainTheory.DataTypesAsLattices.Closures.representClosure_expansive
import DomainTheory.DataTypesAsLattices.Closures.representClosure_idem


namespace DomainTheory.DataTypesAsLattices


























theorem representClosureCode_isClosure
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) :
    IsClosure (representClosureCode D) := by
  constructor
  · intro p hp
    rcases hp with ⟨n, m, rfl, hm⟩
    exact ⟨n, m, rfl, representClosure_expansive D (e n) hm⟩
  · change representClosureCode D =
      graph (fun x => funOf (representClosureCode D)
        (funOf (representClosureCode D) x))
    apply graph_ext
    intro x
    rw [representClosureCode_app, representClosureCode_app,
      representClosure_idem]

end DomainTheory.DataTypesAsLattices
