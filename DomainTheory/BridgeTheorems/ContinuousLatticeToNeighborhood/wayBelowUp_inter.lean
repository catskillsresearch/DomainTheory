module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_23

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
