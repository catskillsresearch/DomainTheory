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
import DomainTheory.DataTypesAsLattices.Functionality.diagC_app
import DomainTheory.DataTypesAsLattices.Functionality.graph_funOf_ext
import DomainTheory.DataTypesAsLattices.Functionality.typed_isGraph
import DomainTheory.DataTypesAsLattices.Functionality.theorem_4_4_med


namespace DomainTheory.DataTypesAsLattices






















/-- **Scott 1976, Theorem 4.4.** The product mediator is unique. -/
theorem theorem_4_4_med_unique {a b c f g h : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (hc : IsRetract c)
    (hf : typed f (arrowR c a)) (hg : typed g (arrowR c b))
    (hh : typed h (arrowR c (tensorR a b)))
    (hfst : comp fstC h = f) (hsnd : comp sndC h = g) :
    h = pairMed f g c := by
  apply graph_funOf_ext (typed_isGraph hh)
    (typed_isGraph (theorem_4_4_med ha hb hc hf hg).1)
  intro x
  have hh' := typed_of_arrowR hh
  have hx : funOf h x =
      funOf (tensorR a b) (funOf h (funOf c x)) := by
    have := congrArg (fun w => funOf w x) hh'
    simpa [comp_app] using this
  have h0 : funOf (funOf h x) (ofNat 0) = funOf f x := by
    have := congrArg (fun w => funOf w x) hfst
    simpa [comp_app, fstC_app] using this
  have h1 : funOf (funOf h x) (ofNat 1) = funOf g x := by
    have := congrArg (fun w => funOf w x) hsnd
    simpa [comp_app, sndC_app] using this
  rw [hx, tensorR_app]
  have hfx : funOf a (funOf (funOf h (funOf c x)) (ofNat 0)) = funOf f x := by
    have h0c : funOf (funOf h (funOf c x)) (ofNat 0) = funOf f (funOf c x) := by
      have := congrArg (fun w => funOf w (funOf c x)) hfst
      simpa [comp_app, fstC_app] using this
    rw [h0c]
    have := congrArg (fun w => funOf w x) (typed_of_arrowR hf)
    simpa [comp_app] using this.symm
  have hgx : funOf b (funOf (funOf h (funOf c x)) (ofNat 1)) = funOf g x := by
    have h1c : funOf (funOf h (funOf c x)) (ofNat 1) = funOf g (funOf c x) := by
      have := congrArg (fun w => funOf w (funOf c x)) hsnd
      simpa [comp_app, sndC_app] using this
    rw [h1c]
    have := congrArg (fun w => funOf w x) (typed_of_arrowR hg)
    simpa [comp_app] using this.symm
  rw [hfx, hgx]
  simp only [pairMed, comp_app, diagC_app, tensorR_app, pairSeq_app_zero,
    pairSeq_app_one]
  have hfr : funOf f (funOf c x) = funOf f x := by
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hf)
    simpa [comp_app] using this.symm
  have hgr : funOf g (funOf c x) = funOf g x := by
    have := congrArg (fun w => funOf w x) (typed_arrowR_restrict hc hg)
    simpa [comp_app] using this.symm
  rw [hfr, hgr]

end DomainTheory.DataTypesAsLattices
