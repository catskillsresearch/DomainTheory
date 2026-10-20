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

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

open Order

/-- Tree / S-expression information system over lower-bound atoms. -/
abbrev SexSys : InfoSys (TreeToken ℕ) :=
  treeSystem lowerBoundSystem

end DomainTheory.BridgeTheorems
