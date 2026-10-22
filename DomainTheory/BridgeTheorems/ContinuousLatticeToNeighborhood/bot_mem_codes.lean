/-ai
The bottom element of a complete lattice belongs to the set of codes of every filter of its way-below neighbourhood system.

The way-below neighbourhood of bottom is the whole carrier, so the master-membership axiom puts it in the filter. Membership of that neighbourhood is the defining condition for bottom to be a code.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_bot
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem bot_mem_codes (f : Filter (D := D)) : (⊥ : D) ∈ codes f := by
  have : f.mem (wayBelowUp (⊥ : D)) := by
    rw [wayBelowUp_bot]
    exact f.master_mem
  exact this

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
