/-ai
The intersection of the way-below neighbourhoods of a and of b equals the way-below neighbourhood of the join of a and b.

If a and b are both way-below an element, then so is their join. Conversely, if the join is way-below an element, then each of a and b is way-below that element because each lies under the join.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem wayBelowUp_inter (a b : D) :
    wayBelowUp a ∩ wayBelowUp b = wayBelowUp (a ⊔ b) := by
  ext z
  constructor
  · exact fun ⟨ha, hb⟩ => WayBelow.sup ha hb
  · intro h
    exact ⟨WayBelow.le_trans le_sup_left h, WayBelow.le_trans le_sup_right h⟩

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
