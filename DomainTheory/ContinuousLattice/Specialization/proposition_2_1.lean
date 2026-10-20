module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
import all Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
import all Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
import all Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
import all Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.Basic
public import DomainTheory.ContinuousLattice.Specialization.proposition_2_1_of_le
public import DomainTheory.ContinuousLattice.Specialization.proposition_2_1_le_of_converges

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]







variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]



variable {x : ι → D} {L y : D}

/-- **Scott 1972, Proposition 2.1.** A monotone net with least upper bound `L` converges to
`y` in the Scott topology iff `y ⊑ L = ⊔ {xᵢ}`. -/
theorem proposition_2_1 [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L) :
    ScottConvergesTo x y ↔ y ≤ L :=
  ⟨fun hconv => proposition_2_1_le_of_converges hL hconv, proposition_2_1_of_le hx hL⟩

end DomainTheory.ContinuousLattice
