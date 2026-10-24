module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainsGivenByNeighbourhoods
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpenu2eisUpperSet
public import DomainTheory.ContinuousLattice.WayBelow.scottOpen_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.directedOn_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_subset
public import DomainTheory.ContinuousLattice.WayBelow.exists_wayBelow_Ici_subset
public import DomainTheory.ContinuousLattice.WayBelow.sInf_wayBelow
public import DomainTheory.ContinuousLattice.WayBelow.isContinuousLattice_iff_isLUB_sInf_nhds

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

theorem toFilter_mono {x y : D} (hxy : x ≤ y) : toFilter x ≤ toFilter y := by
  intro U hU
  obtain ⟨a, ⟨rfl, ha⟩⟩ := hU
  exact ⟨a, ⟨rfl, ha.trans_le hxy⟩⟩

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
