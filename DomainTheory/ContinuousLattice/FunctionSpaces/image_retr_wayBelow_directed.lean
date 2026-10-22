module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


namespace IsContinuousLatticeRetraction


theorem image_retr_wayBelow_directed (R : IsContinuousLatticeRetraction D D') (d : D) :
    DirectedOn (· ≤ ·) (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact ⟨R.retr (a ⊔ b), ⟨a ⊔ b, WayBelow.sup ha hb, rfl⟩,
    R.retr.monotone le_sup_left, R.retr.monotone le_sup_right⟩

end IsContinuousLatticeRetraction
end DomainTheory.ContinuousLattice
