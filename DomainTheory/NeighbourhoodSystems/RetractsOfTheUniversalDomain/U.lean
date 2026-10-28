module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.presentedIntervals
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise_1_19
public import Mathlib.Data.Fintype.Defs

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem

abbrev UMaster : Set ℚ := Set.Ico (0 : ℚ) 1

theorem UMaster_nonempty : UMaster.Nonempty := by
  exact ⟨0, by simp [UMaster]⟩

def UMem (X : Set ℚ) : Prop :=
  (∃ L : List (ℚ × ℚ), X = presentedIntervals L) ∧ X.Nonempty ∧ X ⊆ Set.Ico (0 : ℚ) 1

namespace UMem

theorem sub_master {X : Set ℚ} (hX : UMem X) : X ⊆ UMaster := hX.2.2

theorem master_mem : UMem UMaster :=
  ⟨⟨[(0, 1)], by rw [presentedIntervals.cons, presentedIntervals.nil, Set.union_empty]⟩,
    ⟨0, by norm_num⟩, subset_rfl⟩

theorem inter_mem {X Y Z : Set ℚ} (hX : UMem X) (hY : UMem Y) (hZ : UMem Z)
    (hZsub : Z ⊆ X ∩ Y) : UMem (X ∩ Y) := by
  rcases hX with ⟨⟨L1, rfl⟩, -, hXsub⟩
  rcases hY with ⟨⟨L2, rfl⟩, -, -⟩
  rcases hZ with ⟨-, hZne, -⟩
  exact ⟨⟨combineIntervals L1 L2, presentedIntervals.inter L1 L2⟩,
    hZne.mono hZsub, Set.inter_subset_left.trans hXsub⟩
end UMem

def U : NeighborhoodSystem ℚ where
  mem := UMem
  master := UMaster
  master_nonempty := UMaster_nonempty
  master_mem := UMem.master_mem
  inter_mem := UMem.inter_mem
  sub_master := UMem.sub_master

namespace U

theorem mem_iff_scott {X : Set ℚ} :
    U.mem X ↔ ∃ L : List (ℚ × ℚ), (∀ p ∈ L, (0 : ℚ) ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 1) ∧
      X = presentedIntervals L ∧ X.Nonempty := by
  constructor
  · rintro ⟨⟨L, rfl⟩, hne, hsub⟩
    refine ⟨(L.map clip).filter (fun p => decide (p.1 < p.2)), ?_, ?_, ?_⟩
    · rintro p hp
      obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp1
      exact ⟨le_sup_right, decide_eq_true_eq.mp hp2, inf_le_right⟩
    · rw [presentedIntervals.filter_lt, presentedIntervals.map_clip,
        Set.inter_eq_left.mpr hsub]
    · exact hne
  · rintro ⟨L, hbound, rfl, hne⟩
    refine ⟨⟨L, rfl⟩, hne, ?_⟩
    rintro x hx
    obtain ⟨p, hp, hx1, hx2⟩ := presentedIntervals.mem.mp hx
    obtain ⟨hp0, -, hp1⟩ := hbound p hp
    exact ⟨hp0.trans hx1, hx2.trans_le hp1⟩

theorem no_minimal {X : Set ℚ} (hX : U.mem X) :
    ∃ Y Z : Set ℚ, U.mem Y ∧ U.mem Z ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ Y ≠ X ∧ Z ≠ X := by
  obtain ⟨⟨L, rfl⟩, hne, hsub⟩ := hX
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p, hp, hx1, hx2⟩ := presentedIntervals.mem.mp hx
  have hlt : p.1 < p.2 := lt_of_le_of_lt hx1 hx2
  set m := (p.1 + p.2) / 2 with hm
  have hpm1 : p.1 < m := left_lt_add_div_two.mpr hlt
  have hpm2 : m < p.2 := add_div_two_lt_right.mpr hlt
  have hYZinter : (presentedIntervals L ∩ Set.Iio m) ∩ (presentedIntervals L ∩ Set.Ici m) =
      (∅ : Set ℚ) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨-, h1⟩, -, h2⟩
    exact absurd h1 (not_lt.mpr h2)
  have hYZunion : (presentedIntervals L ∩ Set.Iio m) ∪ (presentedIntervals L ∩ Set.Ici m) =
      presentedIntervals L := by
    ext y
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ici]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases lt_or_ge y m with hlt' | hge'
      · exact Or.inl ⟨h, hlt'⟩
      · exact Or.inr ⟨h, hge'⟩
  have hYne : (presentedIntervals L ∩ Set.Iio m).Nonempty :=
    ⟨p.1, presentedIntervals.mem.mpr ⟨p, hp, le_refl _, hlt⟩, hpm1⟩
  have hZne : (presentedIntervals L ∩ Set.Ici m).Nonempty :=
    ⟨m, presentedIntervals.mem.mpr ⟨p, hp, hpm1.le, hpm2⟩, le_refl m⟩
  refine ⟨_, _, ⟨⟨_, (presentedIntervals.map_clipLt m L).symm⟩, hYne,
      Set.inter_subset_left.trans hsub⟩,
    ⟨⟨_, (presentedIntervals.map_clipGe m L).symm⟩, hZne, Set.inter_subset_left.trans hsub⟩,
    hYZinter, hYZunion, ?_, ?_⟩
  · intro hEq
    have hZsub : presentedIntervals L ∩ Set.Ici m ⊆ presentedIntervals L ∩ Set.Iio m := by
      rw [hEq]; exact Set.inter_subset_left
    exact hZne.ne_empty ((Set.inter_eq_right.mpr hZsub).symm.trans hYZinter)
  · intro hEq
    have hYsub : presentedIntervals L ∩ Set.Iio m ⊆ presentedIntervals L ∩ Set.Ici m := by
      rw [hEq]; exact Set.inter_subset_left
    exact hYne.ne_empty ((Set.inter_eq_left.mpr hYsub).symm.trans hYZinter)

theorem union_mem {X Y : Set ℚ} (hX : X = ∅ ∨ U.mem X) (hY : Y = ∅ ∨ U.mem Y) :
    X ∪ Y = ∅ ∨ U.mem (X ∪ Y) := by
  rcases hX with rfl | hX
  · rcases hY with rfl | hY
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using hY)
  · rcases hY with rfl | hY
    · exact Or.inr (by simpa using hX)
    · obtain ⟨⟨L1, rfl⟩, hXne, hXsub⟩ := hX
      obtain ⟨⟨L2, rfl⟩, hYne, hYsub⟩ := hY
      refine Or.inr ⟨⟨L1 ++ L2, (presentedIntervals.append L1 L2).symm⟩,
        hXne.mono Set.subset_union_left, Set.union_subset hXsub hYsub⟩

theorem iUnion_mem {ι : Type*} [Fintype ι] {f : ι → Set ℚ} (hf : ∀ i, f i = ∅ ∨ U.mem (f i))
    (hne : (⋃ i, f i).Nonempty) : U.mem (⋃ i, f i) := by
  classical
  have hstep : ∀ s : Finset ι, (⋃ i ∈ s, f i) = ∅ ∨ U.mem (⋃ i ∈ s, f i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Or.inl (by simp)
    | insert i s hi ih =>
      rw [Finset.set_biUnion_insert]
      exact union_mem (hf i) ih
  have hall : (⋃ i, f i) = ⋃ i ∈ (Finset.univ : Finset ι), f i := by simp
  rw [hall] at hne ⊢
  exact (hstep Finset.univ).resolve_left hne.ne_empty

theorem diff_mem {X Y : Set ℚ} (hX : U.mem X) (hY : U.mem Y) : X \ Y = ∅ ∨ U.mem (X \ Y) := by
  obtain ⟨⟨L1, rfl⟩, -, hXsub⟩ := hX
  obtain ⟨⟨L2, rfl⟩, -, -⟩ := hY
  rcases Set.eq_empty_or_nonempty (presentedIntervals L1 \ presentedIntervals L2) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨⟨diffLists L1 L2, (presentedIntervals.diffLists L1 L2).symm⟩, h,
      Set.sdiff_subset.trans hXsub⟩

theorem diffClosed : U.DiffClosed := fun hX hY => diff_mem hX hY

theorem isPositive : U.IsPositive := by
  rintro X Y ⟨⟨L1, rfl⟩, -, hXsub⟩ ⟨⟨L2, rfl⟩, -, -⟩
  refine ⟨fun h => h.2.1, fun hne => ⟨⟨combineIntervals L1 L2, presentedIntervals.inter L1 L2⟩,
    hne, Set.inter_subset_left.trans hXsub⟩⟩
theorem noMinimal : U.NoMinimal := by
  intro X hX
  obtain ⟨Y, Z, hY, hZ, hYZinter, hYZunion, -, -⟩ := no_minimal hX
  exact ⟨Y, Z, hY, hZ, hY.2.1, hZ.2.1, hYZinter, hYZunion⟩

end U

end DomainTheory.NeighbourhoodSystems
