/-ai
If a complete lattice D is continuous, the principal filter of an element x is round.

Membership of the neighbourhood of a means a is way-below x. Interpolation of the way-below relation supplies b with a way-below b and b way-below x, so the neighbourhood of b belongs to the principal filter.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.mem_wayBelowUp_toFilter
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.IsRound

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice

open DomainTheory.NeighbourhoodSystems

open scoped DomainTheory.ContinuousLattice

namespace ContinuousLatticeToNeighborhood

variable {D : Type*} [CompleteLattice D]

section Continuous

variable (hD : IsContinuousLattice D)

include hD

theorem toFilter_isRound (x : D) : IsRound (toFilter x) := by
  intro a ha
  have ha' : a ≪ x := mem_wayBelowUp_toFilter.mp ha
  obtain ⟨b, hab, hbx⟩ := wayBelow_interpolate hD ha'
  exact ⟨b, hab, mem_wayBelowUp_toFilter.mpr hbx⟩

end Continuous

end ContinuousLatticeToNeighborhood

end DomainTheory.BridgeTheorems
