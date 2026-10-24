module

public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.wayBelowUp
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpenu2eisUpperSet
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_subset
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_Ici_subset
public import DomainTheory.ContinuousLattice.WayBelow.sInf_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.isContinuousLattice_iff_isLUB_sInf_nhds
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainsGivenByNeighbourhoods

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
