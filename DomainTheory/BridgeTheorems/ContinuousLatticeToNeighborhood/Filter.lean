/-ai
A filter of a complete lattice D is an element of the neighbourhood system whose neighbourhoods are the way-below neighbourhoods on D.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toNeighborhoodSystem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

/-- Filter of the `↟`-neighbourhood system on `D`. -/
abbrev Filter : Type _ :=
  (toNeighborhoodSystem : NeighborhoodSystem D).Element

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
