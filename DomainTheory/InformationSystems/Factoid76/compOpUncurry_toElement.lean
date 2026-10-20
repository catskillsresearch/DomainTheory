/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Proposition56
public import DomainTheory.InformationSystems.Factoid76.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)










theorem compOpUncurry_toElement (g : ApproximableMap B C) (f : ApproximableMap A B)
    (x : A.Element) :
    (compOpUncurry A B C).toElement
      (pairElements (productSystem (functionSystem B C) (functionSystem A B)) A
        (pairElements (functionSystem B C) (functionSystem A B)
          (approxMap_toElement B C g) (approxMap_toElement A B f))
        x) =
      (comp g f).toElement x := by
  let Q := productSystem (functionSystem B C) (functionSystem A B)
  let gf := pairElements (functionSystem B C) (functionSystem A B)
      (approxMap_toElement B C g) (approxMap_toElement A B f)
  have hinner :
      (pairMap (functionSystem A B) A
          (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (sndMap Q A)).toElement
        (pairElements Q A gf x) =
      pairElements (functionSystem A B) A (approxMap_toElement A B f) x := by
    refine element_eq_of_fst_snd (functionSystem A B) A _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem A B) A).toElement
            ((pairMap (functionSystem A B) A
                (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (sndMap Q A)).toElement
              (pairElements Q A gf x)) =
          approxMap_toElement A B f := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          sndMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem A B) A _ _).symm
    · have hL :
          (sndMap (functionSystem A B) A).toElement
            ((pairMap (functionSystem A B) A
                (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (sndMap Q A)).toElement
              (pairElements Q A gf x)) =
          x := by
        rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]
      exact hL.trans (sndMap_pairElements (functionSystem A B) A _ _).symm
  have hf :
      (comp (applyMap (B := A) (C := B))
        (pairMap (functionSystem A B) A
          (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (sndMap Q A))).toElement
        (pairElements Q A gf x) =
      f.toElement x := by
    rw [comp_toElement, hinner, applyMap_toElement, element_toApproxMap_approxMap_toElement]
  have houter :
      (pairMap (functionSystem B C) B
          (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
          (comp (applyMap (B := A) (C := B))
            (pairMap (functionSystem A B) A
              (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
              (sndMap Q A)))).toElement
        (pairElements Q A gf x) =
      pairElements (functionSystem B C) B (approxMap_toElement B C g) (f.toElement x) := by
    refine element_eq_of_fst_snd (functionSystem B C) B _ _ ?_ ?_
    · have hL :
          (fstMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (comp (applyMap (B := A) (C := B))
                  (pairMap (functionSystem A B) A
                    (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                    (sndMap Q A)))).toElement
              (pairElements Q A gf x)) =
          approxMap_toElement B C g := by
        rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
          fstMap_pairElements]
      exact hL.trans (fstMap_pairElements (functionSystem B C) B _ _).symm
    · have hL :
          (sndMap (functionSystem B C) B).toElement
            ((pairMap (functionSystem B C) B
                (comp (fstMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                (comp (applyMap (B := A) (C := B))
                  (pairMap (functionSystem A B) A
                    (comp (sndMap (functionSystem B C) (functionSystem A B)) (fstMap Q A))
                    (sndMap Q A)))).toElement
              (pairElements Q A gf x)) =
          f.toElement x := by
        rw [← comp_toElement, comp_sndMap_pairMap, hf]
      exact hL.trans (sndMap_pairElements (functionSystem B C) B _ _).symm
  simp only [compOpUncurry, comp_toElement]
  rw [houter, applyMap_toElement, element_toApproxMap_approxMap_toElement]

end InfoSys
end DomainTheory.InformationSystems
