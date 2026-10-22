/-ai
Assuming a complete lattice D is a continuous lattice, a round filter is a filter of its way-below neighbourhood system that is round.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Round

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

section Continuous

variable (hD : ContinuousLattice D)

include hD

/-- Round filters of the `↟`-system. -/
abbrev RoundFilter : Type _ :=
  { f : Filter (D := D) // Round f }

end Continuous

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
