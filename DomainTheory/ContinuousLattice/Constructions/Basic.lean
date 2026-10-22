/-ai
Updating one coordinate of a point of a product preserves directed suprema.

At the updated coordinate the update is the identity, so the image of a set is the set itself. At every other coordinate the update is constant, equal to the original point, so the image is a singleton and its supremum is that constant value. The two sides therefore agree coordinatewise.

If an element is way-below a point of a product, then each of its coordinates is way-below the corresponding coordinate of the point.

A Scott-open witness for the product relation pulls back along the update of the given coordinate of the point. The pullback is Scott-open because that update preserves directed suprema. It contains the coordinate of the point, and any value in it has update above the original element, hence is above that element in the chosen coordinate.

A way-below element of a product is bottom off a finite set of coordinates.

The finite truncations of the point, equal to the point on a finite set of coordinates and bottom elsewhere, are monotone, directed, and have the point as supremum. Way-below therefore places the element below some truncation, which forces it to be bottom off that finite set.
ai-/
module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.scottExtend

@[expose] public section

/-!
# Continuous lattice constructions (Scott 1972, §2.8–2.12)

The Milner correction (March 1972, pp. 135–136) is in `MilnerCorrection.lean`. Full proofs of
2.8–2.12 under `CoarserThanScottTopology` are the remaining 1972 items; the Sierpiński
injectivity base case (1.2) is already complete.

This file additionally proves Scott's first two example/closure results, the order-theoretic
content of Propositions 2.8 (finite lattices are continuous) and 2.9 (products of continuous
lattices are continuous). The accompanying topological claims of 2.9–2.10 ("the induced
topology agrees with the product / subspace topology") are the parts that require the Milner
correction and remain open.
-/

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

/-! ### Proposition 2.9(b): the induced topology of a product is the product topology

Scott 1972, Proposition 2.9 also asserts that the Scott topology of the product `∏ᵢ Dᵢ` of
continuous lattices coincides with the topological product of the Scott topologies of the factors.
We prove the two inclusions:

* **Product ⊆ Scott** (`scottTopologicalSpace ≤ Pi.topologicalSpace`): every projection
  `eval i` preserves directed suprema (they are computed coordinatewise), hence is Scott-continuous,
  hence the Scott topology of the product is finer than each induced topology, i.e. finer than their
  infimum (the product topology).
* **Scott ⊆ Product** (`Pi.topologicalSpace ≤ scottTopologicalSpace`): given a Scott-open `U` and a
  point `z ∈ U`, the `↟a` basis (`exists_wayBelow_Ici_subset`) yields `a ≪ z` with `↑a ⊆ U`. A
  way-below element of a product has **finite support** (`wayBelow_finite_support`) and is
  way-below in each coordinate (`wayBelow_proj`); the resulting finite box
  `⋂_{i ∈ F} eval i ⁻¹' (↟aᵢ-neighbourhood of zᵢ)` is a product-open neighbourhood of `z` inside
  `↑a ⊆ U`. -/

/-- Plugging a value into a fixed coordinate, `v ↦ Function.update z i v`, preserves directed
suprema: away from `i` the result is the constant `z j`, and at `i` it is the identity. -/
theorem update_preservesDirectedSup {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, CompleteLattice (E i)] (z : ∀ i, E i) (i : ι) :
    PreservesDirectedSup (fun v : E i => Function.update z i v) := by
  intro T hTne _
  show Function.update z i (sSup T) = sSup ((fun v : E i => Function.update z i v) '' T)
  funext j
  rw [sSup_apply_eq_sSup_image, Set.image_image]
  rcases eq_or_ne j i with hji | hji
  · rw [hji, Function.update_self]
    have h : (fun v : E i => Function.eval i (Function.update z i v)) = id := by
      funext v; simp [Function.eval, Function.update_self]
    rw [h, Set.image_id]
  · rw [Function.update_of_ne hji]
    have h : (fun v : E i => Function.eval j (Function.update z i v)) = fun _ => z j := by
      funext v; simp [Function.eval, Function.update_of_ne hji]
    rw [h, hTne.image_const, sSup_singleton]

/-- A way-below relation in a product projects to each coordinate: if `a ≪ z` in `∏ᵢ Eᵢ` then
`aᵢ ≪ zᵢ`. The witnessing Scott-open neighbourhood of `zᵢ` is the preimage of a product Scott-open
witness under `v ↦ Function.update z i v`, which is Scott-open by `update_preservesDirectedSup`. -/
theorem wayBelow_proj {ι : Type*} {E : ι → Type*} [∀ i, CompleteLattice (E i)]
    {a z : ∀ i, E i} (h : a ≪ z) (i : ι) : a i ≪ z i := by
  classical
  obtain ⟨W, hW, hzW, hWsub⟩ := h
  refine ⟨(fun v : E i => Function.update z i v) ⁻¹' W, ?_, ?_, ?_⟩
  · exact scottOpen_preimage (update_preservesDirectedSup z i) hW
  · show Function.update z i (z i) ∈ W
    rw [Function.update_eq_self]; exact hzW
  · intro v hv
    have hav : a ≤ Function.update z i v := Set.mem_Ici.1 (hWsub hv)
    have := hav i
    rwa [Function.update_self] at this

/-- A way-below element of a product has finite support: if `a ≪ z` in `∏ᵢ Eᵢ` then `aⱼ = ⊥` for
all but finitely many `j`. The finite truncations `Z F = (fun j => if j ∈ F then z j else ⊥)` form a
directed family with supremum `z`; since `a ≪ z = ⊔_F Z F`, already `a ≤ Z F` for some finite `F`,
forcing `aⱼ = ⊥` off `F`. -/
theorem wayBelow_finite_support {ι : Type*} {E : ι → Type*} [∀ i, CompleteLattice (E i)]
    {a z : ∀ i, E i} (h : a ≪ z) : ∃ F : Finset ι, ∀ j ∉ F, a j = ⊥ := by
  classical
  set Z : Finset ι → (∀ j, E j) := fun F j => if j ∈ F then z j else ⊥ with hZ
  set 𝒵 : Set (∀ j, E j) := Set.range Z with h𝒵
  have hmono : Monotone Z := by
    intro F G hFG
    rw [Pi.le_def]; intro j
    simp only [hZ]
    by_cases hjF : j ∈ F
    · rw [ite_eq_left hjF, ite_eq_left (hFG hjF)]
    · rw [ite_eq_right hjF]; exact bot_le
  have h𝒵ne : 𝒵.Nonempty := ⟨Z ∅, ∅, rfl⟩
  have h𝒵dir : DirectedOn (· ≤ ·) 𝒵 := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    exact ⟨Z (F ∪ G), ⟨F ∪ G, rfl⟩, hmono Finset.subset_union_left,
      hmono Finset.subset_union_right⟩
  have hsup : sSup 𝒵 = z := by
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨F, rfl⟩
      rw [Pi.le_def]; intro j
      simp only [hZ]
      by_cases hjF : j ∈ F
      · rw [ite_eq_left hjF]
      · rw [ite_eq_right hjF]; exact bot_le
    · rw [Pi.le_def]; intro j
      rw [sSup_apply_eq_sSup_image]
      refine le_sSup ⟨Z {j}, ⟨{j}, rfl⟩, ?_⟩
      simp [hZ, Function.eval]
  rw [← hsup] at h
  obtain ⟨d, hd𝒵, had⟩ := (wayBelow_sSup_iff h𝒵ne h𝒵dir).1 h
  obtain ⟨F, rfl⟩ := hd𝒵
  refine ⟨F, fun j hjF => ?_⟩
  have hj := had.le j
  simp only [hZ, ite_eq_right hjF] at hj
  exact le_bot_iff.1 hj

/-! ### Proposition 2.11: continuous lattices are injective

The substance of Scott's Theorem 2.12. We give the explicit extension operator
`g(y) = ⊔_{V ∋ y open} ⊓ f''(e⁻¹V)` and prove (a) it extends `f` along an embedding `e`
(using continuity of `D` to interpolate from below) and (b) it is Scott-continuous (using the
`↟a` basis of the Scott topology). -/

section InjectiveExtension

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

end InjectiveExtension
end DomainTheory.ContinuousLattice
