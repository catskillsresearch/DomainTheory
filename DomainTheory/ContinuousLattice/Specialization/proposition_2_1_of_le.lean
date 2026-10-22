/-ai
Scott 1972, Proposition 2.1, backward direction. If y lies below the least upper bound L of a monotone net, then the net converges to y in the Scott topology.

Let U be a Scott-open set containing y. The range of the net is directed: any two indices have a common upper bound, and monotonicity sends the corresponding value above both values. The supremum of the range equals L, so the upper-set property of U and the inequality of y and L put that supremum in U. Scott-openness then supplies a value of the net already in U. From that index onward, monotonicity and the upper-set property keep the net in U.
ai-/
module

public import DomainTheory.ContinuousLattice.WayBelow
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Order.ScottTopology
public import Mathlib.Order.DirSupClosed
public import DomainTheory.ContinuousLattice.Specialization.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

universe u

variable {X : Type*} {D : Type u} [TopologicalSpace X] [CompleteLattice D]


variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]


variable {x : ι → D} {L y : D}

/-- **Scott 1972, Proposition 2.1 (backward).** If `y ≤ L` and `L` is  the lub of a monotone
net, then the net converges to `y` in the Scott topology. -/
theorem proposition_2_1_of_le [Nonempty ι] (hx : IsMonotoneNet x) (hL : IsLUB (range x) L)
    (hyL : y ≤ L) : ScottConvergesTo x y := by
  intro U hU hyU
  have hdir : DirectedOn (· ≤ ·) (range x) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := IsDirected.directed (r := (· ≤ ·)) i j
    exact ⟨x k, ⟨k, rfl⟩, hx hik, hx hjk⟩
  have hLU : sSup (range x) ∈ U := by
    rw [IsLUB.sSup_eq hL]
    exact hU.1 hyL hyU
  obtain ⟨s, hsS, hsU⟩ := hU.2 (Set.range_nonempty x) hdir hLU
  obtain ⟨i₀, rfl⟩ := hsS
  refine ⟨i₀, fun j hj => hU.1 (hx hj) hsU⟩

end DomainTheory.ContinuousLattice
