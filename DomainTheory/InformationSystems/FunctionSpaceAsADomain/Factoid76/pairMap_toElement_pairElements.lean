module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition56
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.constOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOpUncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.pairOp
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOpUncurry
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid76.compOp

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.fstMap_pairElements
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.sndMap_pairElements
@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

open ApproximableMap

variable {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable (A : InfoSys α) (B : InfoSys β) (C : InfoSys γ)

theorem pairMap_toElement_pairElements
    {X : InfoSys α} {Y : InfoSys β} {Z : InfoSys γ}
    (f : ApproximableMap Z X) (g : ApproximableMap Z Y) (z : Z.Element) :
    (pairMap X Y f g).toElement z =
      pairElements X Y (f.toElement z) (g.toElement z) := by
  refine productSystem.element_eq_of_fst_snd X Y _ _ ?_ ?_
  · rw [← comp.toElement, pairMap.comp_fst, fstMap_pairElements]
  · rw [← comp.toElement, pairMap.comp_snd, sndMap_pairElements]

end InfoSys
end DomainTheory.InformationSystems
