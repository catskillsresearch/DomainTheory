/-ai
This file gathers and re-exports the bridges among continuous lattices, neighbourhood systems, and information systems: specialization, domains given by neighbourhoods, information systems, the two directions between neighbourhood systems and information systems, continuous lattices as neighbourhood systems, information systems as ideal completions, ideal completions as continuous lattices, presentation domains, the information-system constructions, the Scott-map bridge, the S-expression domain equation, the worked S-expression example, and the equivalence module.
ai-/
module

public import DomainTheory.ContinuousLattice.Specialization
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.ScottMapBridge
public import DomainTheory.BridgeTheorems.SexDomainEquation
public import DomainTheory.BridgeTheorems.WorkedExampleSExpr
public import DomainTheory.BridgeTheorems.Equivalence

@[expose] public section
