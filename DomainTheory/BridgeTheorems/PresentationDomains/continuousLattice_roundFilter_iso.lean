module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.domainOrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice

@[expose] public section

namespace DomainTheory.BridgeTheorems

open ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D] [DecidableEq D]

noncomputable def continuousLattice_roundFilter_iso (hD : ContinuousLattice D) :
    D ≃o RoundFilter (D := D) :=
  ContinuousLatticeToNeighborhood.domainOrderIso hD

/-- 1972 continuous lattice → 1980 round way-below filters. -/
noncomputable abbrev bridge_1972_1980 {D : Type*} [CompleteLattice D] [DecidableEq D]
    (hD : ContinuousLattice D) :=
  continuousLattice_roundFilter_iso hD

end DomainTheory.BridgeTheorems
