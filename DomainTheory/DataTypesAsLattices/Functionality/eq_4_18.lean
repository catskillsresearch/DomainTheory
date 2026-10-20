/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract


namespace DomainTheory.DataTypesAsLattices















/-- **Scott 1976, (4.18).** `snd ∘ (a ⊗ b) : (a ⊗ b) ∘→ b`. -/
theorem eq_4_18 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp sndC (tensorR a b)) (arrowR (tensorR a b) b) := by
  change comp sndC (tensorR a b) =
    funOf (arrowR (tensorR a b) b) (comp sndC (tensorR a b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  have hab := tensorR_isRetract ha hb
  simp only [comp_app, sndC_app, retract_app hab]
  rw [tensorR_app, pairSeq_app_one, retract_app hb]

end DomainTheory.DataTypesAsLattices
