/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise813a
import DomainTheory.Neighborhood.Exercise813b.Basic


namespace DomainTheory.Neighborhood


















/-- **`Lindenbaum.toSet` is injective.** -/
theorem Lindenbaum.toSet_injective : Function.Injective Lindenbaum.toSet := by
  intro x y
  induction x using Quotient.ind with
  | _ φ =>
    induction y using Quotient.ind with
    | _ ψ =>
      intro h
      exact Quotient.sound (semanticEquiv_iff_evalSet_eq.mpr h)

end DomainTheory.Neighborhood
