module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.WithTopBot
import all Mathlib.Order.Hom.WithTopBot
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
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

/-!
# Worked example — S-expression / tree domain `T ≅ A + (T × T)`

Scott 1982 Factoid 8.1 (`treeSystem`) over the ℕ lower-bound atom system
(Factoid 2.4), walked through this package’s bridges: information system →
neighbourhood filters → ideal completion, plus identity approximable maps as
Scott-continuous maps (Factoid 4.6).
-/

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order

/-! ## Atom system (Factoid 2.4, named) -/


/-! ## S-expression system -/



/-! ## Concrete finite elements -/


/-! ## 1982 → 1980: basic-open neighbourhood filters -/

/-- `|T| ≃o` filters of basic opens `[u]`. -/
noncomputable abbrev sexNeighborhoodIso :
    SexSys.Element ≃o (InfoSysToNeighborhood.toNeighborhoodSystem SexSys).Element :=
  InfoSysToNeighborhood.domainOrderIso SexSys

/-! ## 1982 → ideal completion -/

/-- `|T| ≃o Ideal (FiniteElement T)`. -/
noncomputable abbrev sexIdealIso :
    SexSys.Element ≃o Ideal (InfoSysToIdealCompletion.FiniteElement SexSys) :=
  InfoSysToIdealCompletion.domainOrderIso SexSys

/-- Neighbourhood filters ≃ ideals of finite elements (constructive triangle). -/
noncomputable abbrev sexNeighborhoodIdealIso :=
  neighborhood_ideal_iso SexSys

/-! ## Domain equation at the level of domains (1982 constructions) -/



/-! ## Morphisms: identity is Scott-continuous (Factoid 4.6) -/

/-- Identity approximable map on `T`, as a Scott-continuous endomap. -/
noncomputable abbrev sexIdScottContinuous : ScottContinuous SexSys SexSys :=
  (approximableMap_scottContinuous_equiv SexSys SexSys) (idMap SexSys)
end DomainTheory.BridgeTheorems
