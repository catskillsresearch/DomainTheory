/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.DataTypesAsLattices.Retracts
import DomainTheory.DataTypesAsLattices.Functionality.Basic
import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, (4.34).** `a ∘ outleft ∘ (a ⊕ b) : (a ⊕ b) ∘→ a`. -/
theorem eq_4_34 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp a (comp outleftC (plusR a b))) (arrowR (plusR a b) a) := by
  change comp a (comp outleftC (plusR a b)) =
    funOf (arrowR (plusR a b) a) (comp a (comp outleftC (plusR a b)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha hb), retract_app ha]

end DomainTheory.DataTypesAsLattices
