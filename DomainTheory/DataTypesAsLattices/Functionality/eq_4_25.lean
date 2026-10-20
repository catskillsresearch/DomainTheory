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
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_left
import DomainTheory.DataTypesAsLattices.Functionality.pairSeq_isScottContinuous_right
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_app
import DomainTheory.DataTypesAsLattices.Functionality.tensorR_isRetract
import DomainTheory.DataTypesAsLattices.Functionality.curryC_app


namespace DomainTheory.DataTypesAsLattices

















/-- **Scott 1976, (4.25).**
`curry ∘ ((a ⊗ b) ∘→ c) : ((a ⊗ b) ∘→ c) ∘→ (a ∘→ (b ∘→ c))`. -/
theorem eq_4_25 {a b c : Pomega}
    (ha : IsRetract a) (hb : IsRetract b) (hc : IsRetract c) :
    typed (comp curryC (arrowR (tensorR a b) c))
      (arrowR (arrowR (tensorR a b) c) (arrowR a (arrowR b c))) := by
  change comp curryC (arrowR (tensorR a b) c) =
    funOf (arrowR (arrowR (tensorR a b) c) (arrowR a (arrowR b c)))
      (comp curryC (arrowR (tensorR a b) c))
  rw [arrowR_app]
  have harr := arrowR_isRetract (tensorR_isRetract ha hb) hc
  apply graph_ext
  intro u
  simp only [comp_app]
  rw [retract_app harr]
  have hL :
      funOf curryC (funOf (arrowR (tensorR a b) c) u) =
        graph (fun x => graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))) := by
    rw [curryC_app]
    apply graph_ext
    intro x
    apply graph_ext
    intro y
    rw [arrowR_app]
    simp only [comp_app]
    rw [tensorR_app, pairSeq_app_zero, pairSeq_app_one]
  have hR :
      funOf (arrowR a (arrowR b c))
        (funOf curryC (funOf (arrowR (tensorR a b) c) u)) =
        graph (fun x => graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))) := by
    rw [arrowR_app, hL]
    apply graph_ext
    intro x
    simp only [comp_app]
    have hmid :
        funOf (graph (fun x => graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y)))))) (funOf a x) =
          graph (fun y =>
            funOf c (funOf u (pairSeq (funOf a (funOf a x)) (funOf b y)))) :=
      beta (graph_const_isScottContinuous
        (fun x y => funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))
        (fun y => theorem_1_3 (funOf_isScottContinuous c)
          (theorem_1_3 (funOf_isScottContinuous u)
            (theorem_1_3 (f := fun x => pairSeq x (funOf b y))
              (g := fun x => funOf a x)
              (pairSeq_isScottContinuous_left (funOf b y))
              (funOf_isScottContinuous a))))) (funOf a x)
    rw [hmid, retract_app ha, arrowR_app]
    apply graph_ext
    intro y
    simp only [comp_app]
    have hbeta :
        funOf (graph (fun y =>
          funOf c (funOf u (pairSeq (funOf a x) (funOf b y))))) (funOf b y) =
          funOf c (funOf u (pairSeq (funOf a x) (funOf b (funOf b y)))) :=
      beta (theorem_1_3 (funOf_isScottContinuous c)
        (theorem_1_3 (funOf_isScottContinuous u)
          (theorem_1_3 (f := fun y => pairSeq (funOf a x) y)
            (g := fun y => funOf b y)
            (pairSeq_isScottContinuous_right (funOf a x))
            (funOf_isScottContinuous b)))) (funOf b y)
    rw [hbeta, retract_app hb, retract_app hc]
  exact hL.trans hR.symm

end DomainTheory.DataTypesAsLattices
