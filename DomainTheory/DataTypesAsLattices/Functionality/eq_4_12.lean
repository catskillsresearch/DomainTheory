/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, (4.12).** `(a ⊗ b) ∘ (a' ⊗ b') = (a ∘ a') ⊗ (b ∘ b')`. -/
theorem eq_4_12 (a b a' b' : Pomega) :
    comp (tensorR a b) (tensorR a' b') = tensorR (comp a a') (comp b b') := by
  apply graph_ext
  intro u
  rw [tensorR_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one]
  simp only [comp_app]

end DomainTheory.DataTypesAsLattices
