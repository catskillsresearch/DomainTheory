/-ai
If a lies under b, the way-below neighbourhood of b is contained in the way-below neighbourhood of a.

If b is way-below an element and a lies under b, then a is way-below that element.
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

theorem wayBelowUp_anti {a b : D} (hab : a ≤ b) :
    wayBelowUp b ⊆ wayBelowUp a :=
  fun _ h => WayBelow.le_trans hab h

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
