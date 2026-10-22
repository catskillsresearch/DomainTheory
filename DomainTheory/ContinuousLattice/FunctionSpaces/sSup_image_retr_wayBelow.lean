/-ai
For a continuous-lattice retraction of D' onto D, and an element d of the retract, the supremum in D of the retraction of the set of elements way below the inclusion of d equals d.

The way-below set of the inclusion is nonempty and directed. The retraction preserves its directed supremum, continuity of D' replaces that supremum by the inclusion of d, and the retraction of the inclusion is d.
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


/-- For `d` in the retract, the ambient way-below set of `i(d)` pushed back by `j` is a directed
family whose supremum (computed in `D`) is `d`. This is the identity `j(⊔S′) = ⊔S` applied to
`S = {j(x') : x' ≪ i(d)}`, combined with continuity of `D'`. -/
theorem sSup_image_retr_wayBelow (R : IsContinuousLatticeRetraction D D')
    (hD' : ContinuousLattice D') (d : D) :
    sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) = d := by
  have hne : ({x' : D' | x' ≪ R.incl d}).Nonempty := ⟨⊥, bot_wayBelow _⟩
  have hdir : DirectedOn (· ≤ ·) {x' : D' | x' ≪ R.incl d} := directedOn_wayBelow _
  rw [← R.retr.preservesDirectedSup_coe _ hne hdir, hD'.sSup_wayBelow (R.incl d), R.retr_incl d]

end IsContinuousLatticeRetraction
end DomainTheory.ContinuousLattice
