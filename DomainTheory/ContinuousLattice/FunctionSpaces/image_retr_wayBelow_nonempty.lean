/-ai
For a continuous-lattice retraction and an element d of the retract, the image under the retraction of the set of ambient elements way below the inclusion of d is nonempty.

The bottom element of the ambient lattice is way below the inclusion of d, so its image under the retraction belongs to the set.
ai-/
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


theorem image_retr_wayBelow_nonempty (R : IsContinuousLatticeRetraction D D') (d : D) :
    (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}).Nonempty :=
  ⟨R.retr ⊥, ⊥, bot_wayBelow _, rfl⟩

end IsContinuousLatticeRetraction
end DomainTheory.ContinuousLattice
