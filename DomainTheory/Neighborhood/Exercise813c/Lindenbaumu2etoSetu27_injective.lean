/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Exercise813b
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Clopen
import DomainTheory.Neighborhood.Exercise813c.Basic


namespace DomainTheory.Neighborhood

















theorem Lindenbaum.toSet'_injective : Function.Injective Lindenbaum.toSet' := by
  intro x y
  induction x using Quotient.ind with
  | _ φ =>
    induction y using Quotient.ind with
    | _ ψ =>
      intro h
      exact Quotient.sound (semanticEquiv_iff_evalSet'_eq.mpr h)

end DomainTheory.Neighborhood
