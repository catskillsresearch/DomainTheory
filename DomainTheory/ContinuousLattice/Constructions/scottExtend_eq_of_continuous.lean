/-ai
If the comparison of spaces is an embedding and the map is continuous into a continuous lattice with its Scott topology, the canonical Scott extension agrees with the map on the image of the embedding.

The extension at an image point lies below the original value, because that value belongs to every set whose infimum appears in the supremum. For the reverse, write the value as the supremum of the elements way-below it. The preimage under the map of the Scott-open set of points way-above such an element is open in the subspace, hence is the preimage of an open set in the codomain. On that preimage the map lies above the element, so the element lies below the corresponding infimum and therefore below the extension.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
import all Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]


section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]


/-- The extension agrees with `f` on the (embedded) subspace. The `≤` direction is immediate
(`f x₀` is one of the values being met); the `≥` direction uses continuity of `E`: for each
`a ≪ f x₀` the Scott-open `↟a` pulls back along the continuous `f` and, by the embedding, to an
open `V ⊆ Y` on whose `e`-preimage `f ≥ a`, so `a ≤ ⊓ f''(e⁻¹V) ≤ g(e x₀)`. -/
theorem scottExtend_eq_of_continuous (hE : IsContinuousLattice E) (e : X → Y)
    (he : IsEmbedding e) (f : X → E) (hf : @Continuous X E _ scottTopologicalSpace f) (x₀ : X) :
    scottExtend e f (e x₀) = f x₀ := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro d ⟨V, hVo, hex₀V, rfl⟩
    exact sInf_le ⟨x₀, hex₀V, rfl⟩
  · rw [← hE.sSup_wayBelow (f x₀)]
    refine sSup_le fun a ha => ?_
    have hWopen : @IsOpen E scottTopologicalSpace {z : E | a ≪ z} :=
      isOpen_iff_scottOpen.mpr (scottOpen_wayBelow a)
    have hpre : IsOpen (f ⁻¹' {z : E | a ≪ z}) := continuous_def.mp hf _ hWopen
    rw [he.isInducing.isOpen_iff] at hpre
    obtain ⟨V, hVo, hVeq⟩ := hpre
    have hx₀V : x₀ ∈ e ⁻¹' V := by rw [hVeq]; exact ha
    refine le_trans ?_ (le_sSup ⟨V, hVo, hx₀V, rfl⟩)
    refine le_sInf ?_
    rintro w ⟨x, hxV, rfl⟩
    have hxW : x ∈ f ⁻¹' {z : E | a ≪ z} := by rw [← hVeq]; exact hxV
    exact (hxW : a ≪ f x).le

end InjectiveExtension
end DomainTheory.ContinuousLattice
