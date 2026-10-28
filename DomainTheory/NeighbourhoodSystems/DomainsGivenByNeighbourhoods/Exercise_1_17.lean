module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import Mathlib.Basic.Real.Basic

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace RatInterval
section

open NeighborhoodSystem

def ratIntervalMem (X : Set ℝ) : Prop :=
  X = Set.univ ∨ ∃ a b : ℚ, a < b ∧ X = Set.Ioo (a : ℝ) (b : ℝ)

theorem inter_mem' {X Y : Set ℝ} (hX : ratIntervalMem X) (hY : ratIntervalMem Y)
    (hne : (X ∩ Y).Nonempty) : ratIntervalMem (X ∩ Y) := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · rw [Set.univ_inter]; exact hY
  · rcases hY with rfl | ⟨c, d, hcd, rfl⟩
    · rw [Set.inter_univ]; exact Or.inr ⟨a, b, hab, rfl⟩
    · obtain ⟨z, ⟨hza, hzb⟩, hzc, hzd⟩ := hne
      have had : a < d := by exact_mod_cast hza.trans hzd
      have hcb : c < b := by exact_mod_cast hzc.trans hzb
      have hlt : max a c < min b d := by
        simp only [max_lt_iff, lt_min_iff]
        exact ⟨⟨hab, hcb⟩, had, hcd⟩
      have hset : Set.Ioo (a : ℝ) b ∩ Set.Ioo (c : ℝ) d
          = Set.Ioo ((max a c : ℚ) : ℝ) ((min b d : ℚ) : ℝ) := by
        rw [Set.Ioo_inter_Ioo, Rat.cast_max, Rat.cast_min]
      exact Or.inr ⟨max a c, min b d, hlt, hset⟩

theorem ratIntervalMem_nonempty {X : Set ℝ} (hX : ratIntervalMem X) : X.Nonempty := by
  rcases hX with rfl | ⟨a, b, hab, rfl⟩
  · exact ⟨0, Set.mem_univ 0⟩
  · rw [Set.nonempty_Ioo]; exact_mod_cast hab

def ratIntervalSystem : NeighborhoodSystem ℝ where
  mem := ratIntervalMem
  master := Set.univ
  master_nonempty := Set.univ_nonempty
  master_mem := Or.inl rfl
  inter_mem := by
    intro X Y Z hX hY hZ hZsub
    exact inter_mem' hX hY ((ratIntervalMem_nonempty hZ).mono hZsub)
  sub_master := fun _ => Set.subset_univ _

@[simp] theorem ratIntervalSystem_mem {X : Set ℝ} :
    ratIntervalSystem.mem X ↔ ratIntervalMem X := Iff.rfl

def filterAt (t : ℝ) : ratIntervalSystem.Element where
  mem X := ratIntervalMem X ∧ t ∈ X
  sub h := h.1
  master_mem := ⟨Or.inl rfl, Set.mem_univ t⟩
  inter_mem := by
    rintro X Y ⟨hX, htX⟩ ⟨hY, htY⟩
    exact ⟨inter_mem' hX hY ⟨t, htX, htY⟩, htX, htY⟩
  up_mem := by
    rintro X Y ⟨_, htX⟩ hY hXY
    exact ⟨hY, hXY htX⟩

@[simp] theorem mem_filterAt {t : ℝ} {X : Set ℝ} :
    (filterAt t).mem X ↔ ratIntervalMem X ∧ t ∈ X := Iff.rfl

theorem filterAt_injective {s t : ℝ} (h : filterAt s = filterAt t) : s = t := by
  by_contra hst
  rcases lt_or_gt_of_ne hst with hlt | hlt
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt t
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have htmem : (filterAt t).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [← h] at htmem
    exact absurd htmem.2.1 (not_lt.mpr ha1.le)
  · obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb⟩ := exists_rat_gt s
    have hint : ratIntervalMem (Set.Ioo (a : ℝ) (b : ℝ)) :=
      Or.inr ⟨a, b, by exact_mod_cast ha2.trans hb, rfl⟩
    have hsmem : (filterAt s).mem (Set.Ioo (a : ℝ) (b : ℝ)) := ⟨hint, ha2, hb⟩
    rw [h] at hsmem
    exact absurd hsmem.2.1 (not_lt.mpr ha1.le)
end

end RatInterval
end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.RatInterval
section

set_option linter.unusedVariables false

theorem example_117 : And
  (∀ {s t : Real},
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Real
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalSystem)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt s)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt t) →
      @Eq Real s t)
  (∀ {X Y : Set Real},
    DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem X →
      DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem Y →
        @Set.Nonempty Real (@Inter.inter (Set Real) (@Set.instInter Real) X Y) →
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem
            (@Inter.inter (Set Real) (@Set.instInter Real) X Y)) :=
  @And.intro
  (∀ {s t : Real},
    @Eq
        (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element Real
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalSystem)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt s)
        (DomainTheory.NeighbourhoodSystems.RatInterval.filterAt t) →
      @Eq Real s t)
  (∀ {X Y : Set Real},
    DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem X →
      DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem Y →
        @Set.Nonempty Real (@Inter.inter (Set Real) (@Set.instInter Real) X Y) →
          DomainTheory.NeighbourhoodSystems.RatInterval.ratIntervalMem
            (@Inter.inter (Set Real) (@Set.instInter Real) X Y))
  @DomainTheory.NeighbourhoodSystems.RatInterval.filterAt_injective
  @DomainTheory.NeighbourhoodSystems.RatInterval.inter_mem'
end

end DomainTheory.NeighbourhoodSystems.RatInterval
end
