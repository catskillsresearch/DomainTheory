/-ai
The way-below neighbourhood of the bottom element is the whole carrier.

Every member of the neighbourhood lies in the carrier, and bottom is way-below every element.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem wayBelowUp_bot : wayBelowUp (⊥ : D) = (Set.univ : Set D) := by
  ext z
  exact ⟨fun _ => trivial, fun _ => bot_wayBelow z⟩

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
