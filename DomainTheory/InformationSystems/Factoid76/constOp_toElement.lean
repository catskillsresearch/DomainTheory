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
public import DomainTheory.InformationSystems.Factoid76.pairMap_comp_fst_snd_toElement
public import DomainTheory.InformationSystems.Factoid76.constOp_uncurry

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)




theorem constOp_toElement (b : B.Element) :
    (constOp A B).toElement b =
      approxMap_toElement A B (constMap (A := A) b) := by
  have huniq :
      element_toApproxMap A B ((constOp A B).toElement b) = constMap (A := A) b := by
    refine constMap_unique (A := A) b _ fun x => ?_
    have hpair := pairMap_comp_fst_snd_toElement (constOp A B) b x
    calc
      (element_toApproxMap A B ((constOp A B).toElement b)).toElement x
          = (uncurryMap B A B (constOp A B)).toElement (pairElements B A b x) := by
              simp only [uncurryMap, comp_toElement]
              rw [hpair, applyMap_toElement]
          _ = (fstMap B A).toElement (pairElements B A b x) := by rw [constOp_uncurry]
          _ = b := fstMap_pairElements B A b x
  rw [← huniq, approxMap_toElement_element_toApproxMap]

end InfoSys
end DomainTheory.InformationSystems
