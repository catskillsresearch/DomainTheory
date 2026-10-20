/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_app
import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_bot
import DomainTheory.DataTypesAsLattices.Functionality.sigmaJ_succ_ne


namespace DomainTheory.DataTypesAsLattices


























/-- **Scott 1976, (7.18).** Distinct tags: `σ_j^{m+1}({(j',0)}) = ⊥`. -/
theorem eq_7_18_ne (j j' m : ℕ) (hne : j ≠ j') :
    Z (m + 1) (graph (sigmaJ j)) {pair j' 0} = botElem := by
  induction m with
  | zero =>
    calc
      Z 1 (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j)) {pair j' 0} := rfl
      _ = sigmaJ j {pair j' 0} := sigmaJ_app _ _
      _ = botElem := sigmaJ_succ_ne j j' 0 hne
  | succ m ih =>
    calc
      Z (m + 1 + 1) (graph (sigmaJ j)) {pair j' 0}
        = funOf (graph (sigmaJ j))
            (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) := rfl
      _ = sigmaJ j (Z (m + 1) (graph (sigmaJ j)) {pair j' 0}) :=
          sigmaJ_app _ _
      _ = sigmaJ j botElem := by rw [ih]
      _ = botElem := sigmaJ_bot j

end DomainTheory.DataTypesAsLattices
