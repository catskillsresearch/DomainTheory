module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.Round
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_toFilter
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Order.Directed
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

section Continuous

variable (hD : ContinuousLattice D)

include hD

theorem toFilter_isRound (x : D) : Round (toFilter x) := by
  constructor
  intro a ha
  have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
  obtain ⟨b, hab, hbx⟩ := WayBelow.interpolate hD ha'
  exact ⟨b, hab, mem_wayBelowUp_toFilter.mpr hbx⟩

end Continuous

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
