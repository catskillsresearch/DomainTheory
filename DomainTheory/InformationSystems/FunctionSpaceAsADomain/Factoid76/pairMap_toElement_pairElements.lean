/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

set_option linter.unusedSectionVars false

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)


theorem pairMap_toElement_pairElements
    {X : InfoSys α} {Y : InfoSys β} {Z : InfoSys γ}
    (f : ApproximableMap Z X) (g : ApproximableMap Z Y) (z : Z.Element) :
    (pairMap X Y f g).toElement z =
      pairElements X Y (f.toElement z) (g.toElement z) := by
  refine element_eq_of_fst_snd X Y _ _ ?_ ?_
  · rw [← comp_toElement, comp_fstMap_pairMap, fstMap_pairElements]
  · rw [← comp_toElement, comp_sndMap_pairMap, sndMap_pairElements]

end InfoSys
end DomainTheory.InformationSystems
