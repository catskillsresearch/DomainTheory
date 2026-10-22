module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.sSup_image_retr_wayBelow
public import DomainTheory.ContinuousLattice.FunctionSpaces.image_retr_wayBelow_nonempty
public import DomainTheory.ContinuousLattice.FunctionSpaces.image_retr_wayBelow_directed

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


/-- **Scott 1972, Proposition 2.10(b) (March 1972 / Milner correction).** The Scott topology of the
retract `D` coincides with the subspace topology induced from the ambient `D'` along `i`.

* `scott ≤ induced`: each induced-open `i⁻¹V'` is Scott-open in `D` because `i` is a Scott map.
* `induced ≤ scott`: the sets `i⁻¹(↟x') = {z | x' ≪ i(z)}` (`x' ∈ D'`) are a basis of `D`'s Scott
  topology — given a Scott-open `U ∋ d`, the directed family `{j(x') | x' ≪ i(d)}` (sup `d`) meets
  `U` at some `j(x')`, and `i⁻¹(↟x') ⊆ U` since `x' ≪ i(z) ⟹ j(x') ⊑ z` with `U` upper. Each such
  basic set is induced-open by construction, so every Scott-open of `D` is induced-open. -/
theorem proposition_2_10_b (R : IsContinuousLatticeRetraction D D')
    (hD' : ContinuousLattice D') :
    (scottTopologicalSpace : TopologicalSpace D) =
      TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace := by
  apply le_antisymm
  · intro U hU
    rw [isOpen_induced_iff (t := scottTopologicalSpace)] at hU
    obtain ⟨V', hV'open, rfl⟩ := hU
    rw [isOpen_iff_scottOpen] at hV'open ⊢
    exact scottOpen_preimage R.incl_preservesDirectedSup hV'open
  · intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open _
      (TopologicalSpace.induced (R.incl : D → D') scottTopologicalSpace)]
    intro d hd
    have hmem : sSup (Set.image (R.retr : D' → D) {x' | x' ≪ R.incl d}) ∈ U := by
      rw [R.sSup_image_retr_wayBelow hD' d]; exact hd
    obtain ⟨p, hp, hpU⟩ :=
      hU.2 (R.image_retr_wayBelow_nonempty d) (R.image_retr_wayBelow_directed d) hmem
    obtain ⟨x', hx', rfl⟩ := hp
    refine ⟨(R.incl : D → D') ⁻¹' {z' | x' ≪ z'}, fun z hz => ?_, ?_, hx'⟩
    · have hjle := R.retr.monotone (show x' ≤ R.incl z from (hz : x' ≪ R.incl z).le)
      rw [R.retr_incl z] at hjle
      exact hU.1 hjle hpU
    · rw [isOpen_induced_iff (t := scottTopologicalSpace)]
      exact ⟨{z' | x' ≪ z'}, isOpen_iff_scottOpen.mpr (scottOpen_wayBelow x'), rfl⟩

end DomainTheory.ContinuousLattice
