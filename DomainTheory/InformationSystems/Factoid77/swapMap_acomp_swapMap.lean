/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.Theorem72
public import DomainTheory.InformationSystems.Factoid65
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
public import DomainTheory.InformationSystems.Factoid77.InfoSysObj
public import DomainTheory.InformationSystems.Factoid77.acomp
public import DomainTheory.InformationSystems.Factoid77.id_acomp
public import DomainTheory.InformationSystems.Factoid77.acomp_assoc
public import DomainTheory.InformationSystems.Factoid77.swapMap
public import DomainTheory.InformationSystems.Factoid77.acomp_swap_fst
public import DomainTheory.InformationSystems.Factoid77.acomp_swap_snd

@[expose] public section

set_option linter.unusedSectionVars false

universe u

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace InfoSys

attribute [instance] InfoSysObj.decEq

namespace ApproximableMap

theorem swapMap_acomp_swapMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : InfoSys α) (B : InfoSys β) :
    acomp (swapMap A B) (swapMap B A) = idMap (productSystem A B) := by
  have hfst : acomp (acomp (swapMap A B) (swapMap B A)) (fstMap A B) = fstMap A B := by
    calc
      acomp (acomp (swapMap A B) (swapMap B A)) (fstMap A B)
          = acomp (swapMap A B) (acomp (swapMap B A) (fstMap A B)) := acomp_assoc _ _ _
      _ = acomp (swapMap A B) (sndMap B A) := by rw [acomp_swap_fst]
      _ = fstMap A B := acomp_swap_snd A B
  have hsnd : acomp (acomp (swapMap A B) (swapMap B A)) (sndMap A B) = sndMap A B := by
    calc
      acomp (acomp (swapMap A B) (swapMap B A)) (sndMap A B)
          = acomp (swapMap A B) (acomp (swapMap B A) (sndMap A B)) := acomp_assoc _ _ _
      _ = acomp (swapMap A B) (fstMap B A) := by rw [acomp_swap_snd]
      _ = sndMap A B := acomp_swap_fst A B
  exact (pairMap_unique A B (fstMap A B) (sndMap A B) _ hfst hsnd).trans
    (pairMap_unique A B (fstMap A B) (sndMap A B) (idMap _)
      (id_acomp _) (id_acomp _)).symm

end ApproximableMap

end InfoSys

end DomainTheory.InformationSystems
