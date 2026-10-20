/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Proposition56
import DomainTheory.InformationSystems.Factoid76.Basic


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


theorem pairMap_comp_fst_snd_toElement
    {P : InfoSys α} {X : InfoSys β} {Y : InfoSys γ}
    (k : ApproximableMap P (functionSystem Y X))
    (p : P.Element) (y : Y.Element) :
    (pairMap (functionSystem Y X) Y (comp k (fstMap P Y)) (sndMap P Y)).toElement
      (pairElements P Y p y) =
      pairElements (functionSystem Y X) Y (k.toElement p) y := by
  refine element_eq_of_fst_snd (functionSystem Y X) Y _ _ ?_ ?_
  · rw [← comp_toElement, comp_fstMap_pairMap, comp_toElement, fstMap_pairElements,
      fstMap_pairElements]
  · rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements, sndMap_pairElements]

end InfoSys
end DomainTheory.InformationSystems
