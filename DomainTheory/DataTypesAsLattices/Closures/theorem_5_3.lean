/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Algebra.Ring.Parity
import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Closures.Basic


namespace DomainTheory.DataTypesAsLattices


















/-- **Scott 1976, Theorem 5.3 (The function space theorem for algebraic
lattices).** The function-space retract of two closures is a retract. -/
theorem theorem_5_3 {a b : Pomega} (ha : IsClosure a) (hb : IsClosure b) :
    IsRetract (arrowR a b) := by
  change arrowR a b = graph (fun x => funOf (arrowR a b) (funOf (arrowR a b) x))
  apply graph_ext
  intro u
  rw [theorem_4_3_i ha.2 hb.2, arrowR_app]

end DomainTheory.DataTypesAsLattices
