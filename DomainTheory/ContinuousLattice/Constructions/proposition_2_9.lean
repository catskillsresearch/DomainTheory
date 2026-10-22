/-ai
The Cartesian product of any family of continuous lattices is a continuous lattice whose induced Scott topology agrees with the product topology.

An upper bound of the elements way-below a point of the product lies above the point. At each coordinate, write the coordinate of the point as the supremum of the elements way-below it. The cylinder that carries such an element in that coordinate and bottom elsewhere is way-below the point: the preimage of a Scott-open witness under evaluation at the coordinate is Scott-open in the product, because suprema and directedness are computed coordinatewise, and the cylinder lies below every point of that preimage. The cylinder therefore lies below the upper bound, so the element lies below the upper bound in that coordinate. Ranging over all such elements, the coordinate of the point, being their supremum, lies below the upper bound.

The product topology is coarser than the Scott topology because each projection preserves directed suprema and is therefore Scott-continuous. Conversely, if a Scott-open set contains a point, the way-below basis supplies an element way-below that point whose principal upset lies in the open set. The element has finite support and is way-below the point in each coordinate. The finite box cut out by the chosen coordinate neighbourhoods is product-open, contains the point, and lies inside the upset, hence inside the open set.
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

/-- **Scott 1972, Proposition 2.9.** The Cartesian product of any family of continuous lattices is a
continuous lattice whose Scott topology agrees with the product topology. -/
theorem proposition_2_9 {ι : Type*} (E : ι → Type*) [∀ i, CompleteLattice (E i)]
    (hE : ∀ i, ContinuousLattice (E i)) :
    ContinuousLattice (∀ i, E i) ∧
      (scottTopologicalSpace : TopologicalSpace (∀ i, E i)) =
        @Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace) := by
  classical
  have hprod : ContinuousLattice (∀ i, E i) := by
    constructor
    intro y
    refine ⟨fun x hx => hx.le, fun b hb => ?_⟩
    rw [Pi.le_def]
    intro i
    rw [← (hE i).sSup_wayBelow (y i)]
    apply sSup_le
    intro a ha
    set e : (∀ j, E j) := Function.update (⊥ : ∀ j, E j) i a with he
    have hei : e i = a := by rw [he]; exact Function.update_self i a _
    have hcyl : e ≪ y := by
      obtain ⟨U, hU, hyiU, hUsub⟩ := ha
      refine ⟨{z : ∀ j, E j | z i ∈ U}, ?_, hyiU, ?_⟩
      · refine ⟨fun z w hzw hz => hU.1 (hzw i) hz, fun S hSne hSdir hmem => ?_⟩
        rw [Set.mem_ofPred_eq, sSup_apply_eq_sSup_image] at hmem
        have hdir' : DirectedOn (· ≤ ·) (Function.eval i '' S) := by
          rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
          obtain ⟨h, hhS, hfh, hgh⟩ := hSdir f hf g hg
          exact ⟨Function.eval i h, ⟨h, hhS, rfl⟩, hfh i, hgh i⟩
        obtain ⟨t, htimg, htU⟩ := hU.2 (hSne.image _) hdir' hmem
        obtain ⟨f, hfS, rfl⟩ := htimg
        exact ⟨f, hfS, htU⟩
      · intro z hz
        rw [Set.mem_Ici, Pi.le_def]
        intro j
        rcases eq_or_ne j i with rfl | hji
        · rw [hei]; exact Set.mem_Ici.1 (hUsub hz)
        · rw [he, Function.update_of_ne hji]; exact bot_le
    have hle : e i ≤ b i := (hb hcyl) i
    rw [hei] at hle
    exact hle
  refine ⟨hprod, ?_⟩
  apply le_antisymm
  · refine le_iInf fun i => ?_
    rw [← continuous_iff_le_induced]
    exact continuous_of_preservesDirectedSup (fun _ _ _ => sSup_apply_eq_sSup_image)
  · intro U hU
    rw [isOpen_iff_scottOpen] at hU
    rw [@isOpen_iff_forall_mem_open _ (@Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace))]
    intro z hz
    obtain ⟨a, haz, haIci⟩ := exists_wayBelow_Ici_subset hprod hU hz
    obtain ⟨F, hF⟩ := wayBelow_finite_support haz
    have hproj : ∀ i, a i ≪ z i := fun i => wayBelow_proj haz i
    choose V hVopen hzV hVsub using hproj
    refine ⟨⋂ i ∈ F, (fun w : ∀ j, E j => w i) ⁻¹' V i, ?_, ?_, ?_⟩
    · intro w hw
      rw [Set.mem_iInter₂] at hw
      refine haIci (Set.mem_Ici.2 fun j => ?_)
      by_cases hjF : j ∈ F
      · exact Set.mem_Ici.1 (hVsub j (hw j hjF))
      · rw [hF j hjF]; exact bot_le
    · refine @isOpen_biInter_finset (∀ j, E j) ι
        (@Pi.topologicalSpace ι E (fun _ => scottTopologicalSpace)) F
        (fun i => (fun w : ∀ j, E j => w i) ⁻¹' V i) (fun i _ => ?_)
      have hVi : @IsOpen (E i) scottTopologicalSpace (V i) := isOpen_iff_scottOpen.mpr (hVopen i)
      have hind : @IsOpen _
          (TopologicalSpace.induced (fun w : ∀ j, E j => w i) scottTopologicalSpace)
          ((fun w : ∀ j, E j => w i) ⁻¹' V i) :=
        (isOpen_induced_iff (t := scottTopologicalSpace)).mpr ⟨V i, hVi, rfl⟩
      exact iInf_le
        (fun i => TopologicalSpace.induced (fun w : ∀ j, E j => w i) scottTopologicalSpace) i _ hind
    · rw [Set.mem_iInter₂]
      exact fun i _ => hzV i

end DomainTheory.ContinuousLattice
