/-ai
A continuous map into a continuous lattice, taken with its Scott topology, sends a point to the supremum of the infima of the map over the open neighbourhoods of the point.

For the lower bound, write the value as the supremum of the elements way-below it. The preimage of the Scott-open set of points way-above such an element is an open neighbourhood of the point, and the element lies below every value on that preimage, hence below the infimum. For the upper bound, each such infimum lies below the value because the point belongs to the neighbourhood.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]


/-- For a continuous `f' : Y → E` into a continuous lattice `E` (with its Scott topology), the
value `f' y` is reconstructed as the supremum over open neighbourhoods `U ∋ y` of the meets
`⊓ f''(U)`. This is the order-theoretic content behind the maximality clause of Proposition 3.8:
the `≤` direction interpolates from below using `f' y = ⊔ {a | a ≪ f' y}` and the openness of each
`f'⁻¹(↟a)`; the `≥` direction is immediate since `f' y ∈ f''(U)` whenever `y ∈ U`. -/
theorem continuous_eq_sSup_openInfs (hE : ContinuousLattice E) {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (y : Y) :
    f' y = sSup {d | ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧ d = sInf (f' '' U)} := by
  apply le_antisymm
  · rw [← hE.sSup_wayBelow (f' y)]
    refine sSup_le fun a ha => ?_
    have hWopen : @IsOpen E scottTopologicalSpace {z : E | a ≪ z} :=
      isOpen_iff_scottOpen.mpr (scottOpen_wayBelow a)
    have hpre : IsOpen (f' ⁻¹' {z : E | a ≪ z}) := continuous_def.mp hf' _ hWopen
    have hyU : y ∈ f' ⁻¹' {z : E | a ≪ z} := ha
    refine le_trans ?_ (le_sSup ⟨f' ⁻¹' {z : E | a ≪ z}, hpre, hyU, rfl⟩)
    refine le_sInf ?_
    rintro w ⟨z, hzU, rfl⟩
    exact (hzU : a ≪ f' z).le
  · refine sSup_le ?_
    rintro d ⟨U, _hUo, hyU, rfl⟩
    exact sInf_le ⟨y, hyU, rfl⟩

end InjectiveExtension
end DomainTheory.ContinuousLattice
