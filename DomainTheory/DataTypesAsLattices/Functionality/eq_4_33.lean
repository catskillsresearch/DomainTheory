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
import DomainTheory.DataTypesAsLattices.Functionality.plusR_app
import DomainTheory.DataTypesAsLattices.Functionality.inrightC_app


namespace DomainTheory.DataTypesAsLattices

















/-- **Scott 1976, (4.33).** ` (a ⊕ b) ∘ inright ∘ b : b ∘→ (a ⊕ b) `. -/
theorem eq_4_33 {a b : Pomega} (hb : IsRetract b) :
    typed (comp (plusR a b) (comp inrightC b)) (arrowR b (plusR a b)) := by
  change comp (plusR a b) (comp inrightC b) =
    funOf (arrowR b (plusR a b)) (comp (plusR a b) (comp inrightC b))
  rw [arrowR_app]
  apply graph_ext
  intro x
  simp only [comp_app, inrightC_app, retract_app hb]
  rw [plusR_app, plusR_app, pairSeq_app_zero, pairSeq_app_one,
    dcondSet_ofNat_one, retract_app hb]
  rw [pairSeq_app_zero, pairSeq_app_one, dcondSet_ofNat_one, retract_app hb]

end DomainTheory.DataTypesAsLattices
