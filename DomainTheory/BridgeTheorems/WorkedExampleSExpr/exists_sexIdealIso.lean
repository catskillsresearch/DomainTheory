/-ai
There is an order isomorphism between the elements of the S-expression system and the ideals of its finite elements.

The ideal isomorphism of the worked example is a witness.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.InformationSystems.Factoid24
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.ScottMapBridge
public import DomainTheory.BridgeTheorems.SexDomainEquation
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.Basic

@[expose] public section


namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order


theorem exists_sexIdealIso :
    Nonempty (SexSys.Element ≃o
      Ideal (InfoSysToIdealCompletion.FiniteElement SexSys)) :=
  ⟨sexIdealIso⟩

end DomainTheory.BridgeTheorems
