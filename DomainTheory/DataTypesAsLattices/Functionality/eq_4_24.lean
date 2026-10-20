/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Functionality.Basic
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_zero
public import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_app_one
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
public import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
public import DomainTheory.DataTypesAsLattices.Functionality.evalC_app

@[expose] public section


namespace DomainTheory.DataTypesAsLattices

















/-- **Scott 1976, (4.24).** `eval ∘ ((b ∘→ c) ⊗ b) : ((b ∘→ c) ⊗ b) ∘→ c`. -/
theorem eq_4_24 {b c : Pomega} (hb : IsRetract b) (hc : IsRetract c) :
    typed (comp evalC (tensorR (arrowR b c) b))
      (arrowR (tensorR (arrowR b c) b) c) := by
  change comp evalC (tensorR (arrowR b c) b) =
    funOf (arrowR (tensorR (arrowR b c) b) c)
      (comp evalC (tensorR (arrowR b c) b))
  rw [arrowR_app]
  apply graph_ext
  intro u
  have hL :
      funOf evalC (funOf (tensorR (arrowR b c) b) u) =
        funOf c (funOf (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) := by
    rw [evalC_app, tensorR_app, pairSeq_app_zero, pairSeq_app_one, arrowR_app]
    simp only [comp_app]
    rw [retract_app hb]
  have hR :
      funOf c (funOf evalC (funOf (tensorR (arrowR b c) b)
        (funOf (tensorR (arrowR b c) b) u))) =
        funOf c (funOf (funOf u (ofNat 0)) (funOf b (funOf u (ofNat 1)))) := by
    have hten := retract_app (tensorR_isRetract (arrowR_isRetract hb hc) hb) u
    rw [hten, hL, retract_app hc]
  simp only [comp_app]
  exact hL.trans hR.symm

end DomainTheory.DataTypesAsLattices
