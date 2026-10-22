module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.scottExtend

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

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

end DomainTheory.ContinuousLattice
