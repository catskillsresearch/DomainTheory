module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp_inter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Filter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.codes

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem codes_directed (f : Filter (D := D)) : DirectedOn (· ≤ ·) (codes f) := by
  intro a ha b hb
  refine ⟨a ⊔ b, ?_, le_sup_left, le_sup_right⟩
  have : f.mem (wayBelowUp a ∩ wayBelowUp b) := f.inter_mem ha hb
  rwa [wayBelowUp_inter] at this

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
