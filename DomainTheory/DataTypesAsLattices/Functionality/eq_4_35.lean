/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.plusR_isRetract

@[expose] public section


namespace DomainTheory.DataTypesAsLattices





















/-- **Scott 1976, (4.35).** `b ∘ outright ∘ (a ⊕ b) : (a ⊕ b) ∘→ b`. -/
theorem eq_4_35 {a b : Pomega} (ha : IsRetract a) (hb : IsRetract b) :
    typed (comp b (comp outrightC (plusR a b))) (arrowR (plusR a b) b) := by
  change comp b (comp outrightC (plusR a b)) =
    funOf (arrowR (plusR a b) b) (comp b (comp outrightC (plusR a b)))
  rw [arrowR_app]
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app (plusR_isRetract ha hb), retract_app hb]

end DomainTheory.DataTypesAsLattices
