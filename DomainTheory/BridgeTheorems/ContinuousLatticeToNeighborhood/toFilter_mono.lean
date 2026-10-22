module

public import Mathlib.Order.Hom.Basic
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.BridgeTheorems.ContinuousLatticeToNeighborhood.toFilter

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
