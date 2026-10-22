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
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.lowerBoundSystem
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexAtom
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexRhsSemanticIso
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.sexDomainEquationIso
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexSys
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr.SexRhs

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order


/-- `|T| ≃o` filters of basic opens `[u]`. -/
noncomputable abbrev sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element :=
  InfoSysToNeighborhood.domainOrderIso SexSys

/-- `|T| ≃o Ideal (FiniteElement T)`. -/
noncomputable abbrev sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) :=
  InfoSysToIdealCompletion.domainOrderIso SexSys

/-- Neighbourhood filters ≃ ideals of finite elements (constructive triangle). -/
noncomputable abbrev sexNeighborhoodIdealIso :=
  neighborhood_ideal_iso SexSys


/-- Identity approximable map on `T`, as a Scott-continuous endomap. -/
noncomputable abbrev sexIdScottContinuous : ScottContinuous SexSys SexSys :=
  (approximableMap_scottContinuous_equiv SexSys SexSys) (idMap SexSys)
end DomainTheory.BridgeTheorems
