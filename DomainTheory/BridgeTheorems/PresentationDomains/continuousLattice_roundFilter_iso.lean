/-ai
The order isomorphism between a continuous lattice and its round way-below filters is the domain order isomorphism of the passage from the continuous lattice to its way-below neighbourhood system.
ai-/
module

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

variable (hD : IsContinuousLattice D)

include hD

/-- **1972 ↔ round 1980:** continuous lattice ↔ round `↟`-filters. -/
noncomputable def continuousLattice_roundFilter_iso :
    D ≃o RoundFilter (D := D) :=
  ContinuousLatticeToNeighborhood.domainOrderIso hD

end Continuous

end DomainTheory.BridgeTheorems
