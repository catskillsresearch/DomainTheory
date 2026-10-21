/-ai
Pairing the composite of a map k with the first projection and the second projection, and evaluating at the pair of an element p with an element y, yields the pair of the value of k at p with y.

The two sides have equal first projections and equal second projections, by the projection laws for a pairing, for composition, and for a paired element.
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
