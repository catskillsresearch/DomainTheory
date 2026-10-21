/-ai
The codes of a filter of the way-below neighbourhood system are the elements whose way-below neighbourhood belongs to the filter.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- Codes whose `↟`-neighbourhoods lie in the filter. -/
def codes (f : Filter (D := D)) : Set D :=
  {a : D | f.mem (wayBelowUp a)}

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
