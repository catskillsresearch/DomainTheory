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
import DomainTheory.DataTypesAsLattices.Retracts.arrowR_app


namespace DomainTheory.DataTypesAsLattices









































/-- **Scott 1976, (4.11).** Composition of function-space retracts. -/
theorem eq_4_11_comp (a b a' b' : Pomega) :
    comp (arrowR a b) (arrowR a' b') = arrowR (comp a' a) (comp b b') := by
  apply graph_ext
  intro u
  calc
    funOf (arrowR a b) (funOf (arrowR a' b') u)
        = comp b (comp (funOf (arrowR a' b') u) a) := arrowR_app _ _ _
    _ = comp b (comp (comp b' (comp u a')) a) := by rw [arrowR_app]
    _ = comp (comp b b') (comp u (comp a' a)) := by
      apply graph_ext
      intro x
      simp only [comp_app]

end DomainTheory.DataTypesAsLattices
