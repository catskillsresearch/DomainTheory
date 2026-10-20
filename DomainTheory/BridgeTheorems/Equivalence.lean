module

public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains
public import DomainTheory.BridgeTheorems.InfoSysConstructions
public import DomainTheory.BridgeTheorems.ScottMapBridge

@[expose] public section

/-!
# Equivalence theorems

Bridges between Scott's 1972 continuous-lattice presentation, 1980 neighbourhood systems
(PRG-19), and 1982 information systems. Sibling packages are finished; this module holds
the cross-presentation maps. See `arxiv.md` / `HANDOFF.md`.

## Status

* `neighborhoodSystem_to_infoSys` — **done** (`NeighborhoodToInfoSys.lean`)
* `infoSys_to_neighborhoodSystem` — **done** (`InfoSysToNeighborhood.lean`)
* `continuousLattice_to_neighborhoodSystem` — **done** (`ContinuousLatticeToNeighborhood.lean`;
  `D ≃o RoundFilter`, not raw `|𝒟|`)
* `infoSys_to_idealCompletion` — **done** (`InfoSysToIdealCompletion.lean`;
  `|A| ≃o Ideal (FiniteElement A)`)
* `idealCompletion_to_continuousLattice` — **done** (`IdealCompletionToContinuousLattice.lean`;
  algebraic complete lattice ⇒ `IsContinuousLattice`; classical `≪`)
* `presentation_domains_equiv` — **done** (`PresentationDomains.lean`;
  `D ≃o RoundFilter ≃o RoundInfoSysElement` via `wayBelowNbhdBasis`)
* `infoSys_constructions_equiv` — **done** (`InfoSysConstructions.lean` +
  `ScottMapBridge.lean`; 1982 product/sum/function-space domain isos;
  `ApproximableMap ≃o ScottContinuous`; `ScottMap` conjugates along round presentation)
* worked example — **done** (`WorkedExampleSExpr.lean`; Factoid 8.1 trees through
  neighbourhood / ideal bridges + domain-equation iso)
-/
