/-ai
The pairing of approximable maps f and g, evaluated at an element z, is the pair of their evaluations at z.

The two sides have equal first projections and equal second projections, by the projection laws for a pairing and for a paired element.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.Basic

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.fstMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.sndMap_pairElements
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
