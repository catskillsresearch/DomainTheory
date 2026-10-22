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

public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid81.treeUnfold_atom
@[expose] public section


namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems
open DomainTheory.InformationSystems.Constructive
open DomainTheory.InformationSystems.InfoSys
open DomainTheory.InformationSystems.InfoSys.ApproximableMap
open Order


/-- Unfolding tokens into the sum-of-product carrier (Factoid 8.1). -/
theorem sexUnfold_atom (n : ℕ) :
    treeUnfold lowerBoundSystem (.atom n) = SumToken.left n :=
  treeUnfold_atom lowerBoundSystem n

end DomainTheory.BridgeTheorems
