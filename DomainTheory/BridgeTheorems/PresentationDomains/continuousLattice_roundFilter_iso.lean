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

open DomainTheory.InformationSystems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open Order

open scoped DomainTheory.ContinuousLattice

open ContinuousLatticeToNeighborhood

universe u

variable {D : Type u} [CompleteLattice D] [DecidableEq D]

section Continuous

variable (hD : ContinuousLattice D)

include hD

noncomputable def continuousLattice_roundFilter_iso :
    D ≃o RoundFilter (D := D) :=
  ContinuousLatticeToNeighborhood.domainOrderIso hD

end Continuous

end DomainTheory.BridgeTheorems
