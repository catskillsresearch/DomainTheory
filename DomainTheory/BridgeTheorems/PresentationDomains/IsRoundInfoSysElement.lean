/-ai
An element of the information system induced by the way-below neighbourhood basis is round when the filter corresponding to it under the inverse domain isomorphism is a round filter.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.BridgeTheorems.InfoSysToNeighborhood
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion
public import DomainTheory.BridgeTheorems.NeighborhoodToInfoSys
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood
public import DomainTheory.BridgeTheorems.IdealCompletionToContinuousLattice
public import DomainTheory.BridgeTheorems.PresentationDomains.wayBelowNbhdBasis

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

/-- Roundness transported to InfoSys elements of the `↟`-basis. -/
class IsRoundInfoSysElement (e : (wayBelowNbhdBasis (D := D)).toInfoSys.Element) : Prop where
  out : Round ((wayBelowNbhdBasis (D := D)).domainOrderIso.symm e)

end DomainTheory.BridgeTheorems
