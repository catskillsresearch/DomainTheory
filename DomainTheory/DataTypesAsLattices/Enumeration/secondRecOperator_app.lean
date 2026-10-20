/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import Mathlib.Computability.Halting
import DomainTheory.DataTypesAsLattices.Computability
import DomainTheory.DataTypesAsLattices.Functionality
import DomainTheory.DataTypesAsLattices.Enumeration.Basic
import DomainTheory.DataTypesAsLattices.Enumeration.secondRecSubstC_realizes


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices














































theorem secondRecOperator_app (u : Pomega) :
    funOf secondRecOperator u = secondRecVal u := by
  have hsubst :
      (Scomb ⬝ (Scomb ⬝ (Kcomb ⬝ Scomb) ⬝ Kcomb) ⬝ (Kcomb ⬝ secondRecSubstC)) ⬝ u =
        Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC := by
    rw [Scomb_beta3, Kcomb_beta2, SK_comp]
  rw [secondRecOperator, SK_comp, hsubst, dollarC_app]
  apply congrArg graph
  funext x
  have hreal (m : ℕ) :
      (Scomb ⬝ (Kcomb ⬝ u) ⬝ secondRecSubstC) ⬝ ofNat m =
        u ⬝ ofNat (secondRecSubst m) := by
    rw [SK_comp, secondRecSubstC_realizes]
  ext k
  simp [seqFun, hreal, secondRecSubst]

end DomainTheory.DataTypesAsLattices
