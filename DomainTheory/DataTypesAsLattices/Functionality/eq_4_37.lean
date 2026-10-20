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





















/-- **Scott 1976, (4.37).** `a ∘ out ∘ (a ⊕ a) : (a ⊕ a) ∘→ a`. -/
theorem eq_4_37 {a : Pomega} (ha : IsRetract a) :
    typed (comp a (comp outC (plusR a a))) (arrowR (plusR a a) a) := by
  change comp a (comp outC (plusR a a)) =
    funOf (arrowR (plusR a a) a) (comp a (comp outC (plusR a a)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha ha), retract_app ha]

end DomainTheory.DataTypesAsLattices
