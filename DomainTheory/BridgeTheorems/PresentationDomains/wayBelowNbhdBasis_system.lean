/-ai
The neighbourhood system of the way-below neighbourhood basis is the way-below neighbourhood system.

The two sides are identical by the definition of the basis.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.Basic

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


theorem wayBelowNbhdBasis_system :
    (wayBelowNbhdBasis (D := D)).system = toNeighborhoodSystem :=
  rfl

end DomainTheory.BridgeTheorems
