/-ai
The order isomorphism between a continuous lattice and the round elements of the information system of its way-below basis is the composite of the isomorphism with the round way-below filters and the isomorphism from those round filters to the round information-system elements.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.RoundInfoSysElement
public import DomainTheory.BridgeTheorems.PresentationDomains.roundFilter_infoSys_iso
public import DomainTheory.BridgeTheorems.PresentationDomains.continuousLattice_roundFilter_iso

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

/-- **1972 ↔ round 1982:** continuous lattice ↔ round InfoSys elements of the `↟`-basis. -/
noncomputable def continuousLattice_roundInfoSys_iso :
    D ≃o RoundInfoSysElement (D := D) :=
  (continuousLattice_roundFilter_iso hD).trans roundFilter_infoSys_iso

end Continuous

end DomainTheory.BridgeTheorems
