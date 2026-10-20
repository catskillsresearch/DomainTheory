/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.InformationSystems.Theorem72
import DomainTheory.InformationSystems.Proposition56
import DomainTheory.InformationSystems.Factoid76.Basic
import DomainTheory.InformationSystems.Factoid76.pairMap_comp_fst_snd_toElement
import DomainTheory.InformationSystems.Factoid76.pairOp_uncurry
import DomainTheory.InformationSystems.Factoid76.pairOpUncurry_toElement


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)







theorem pairOp_toElement (f : ApproximableMap C A) (g : ApproximableMap C B) :
    (pairOp A B C).toElement
      (pairElements (functionSystem C A) (functionSystem C B)
        (approxMap_toElement C A f) (approxMap_toElement C B g)) =
      approxMap_toElement C (productSystem A B) (pairMap A B f g) := by
  let P := productSystem (functionSystem C A) (functionSystem C B)
  let fg := pairElements (functionSystem C A) (functionSystem C B)
      (approxMap_toElement C A f) (approxMap_toElement C B g)
  have huniq :
      element_toApproxMap C (productSystem A B) ((pairOp A B C).toElement fg) =
        pairMap A B f g := by
    refine (ext_iff_toElement _ _).2 fun x => ?_
    have hpair :=
      pairMap_comp_fst_snd_toElement (X := productSystem A B) (pairOp A B C) fg x
    calc
      (element_toApproxMap C (productSystem A B) ((pairOp A B C).toElement fg)).toElement x
          = (uncurryMap P C (productSystem A B) (pairOp A B C)).toElement
              (pairElements P C fg x) := by
              simp only [uncurryMap, comp_toElement]
              rw [hpair, applyMap_toElement]
          _ = (pairOpUncurry A B C).toElement (pairElements P C fg x) := by
              rw [pairOp_uncurry]
          _ = (pairMap A B f g).toElement x := pairOpUncurry_toElement A B C f g x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

end InfoSys
end DomainTheory.InformationSystems
