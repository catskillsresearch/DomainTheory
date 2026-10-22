module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Lattice.Bounded
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Finset
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition87.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **Scott's remark after Definition 8.7**: "`U` has no minimal neighbourhoods: every set in `U`
can be written as the union of two disjoint sets in `U`." Splitting at the rational midpoint `m`
of any interval witnessing `X`'s non-emptiness realizes `X` as `Y ⊔ Z` for `U`-neighbourhoods
`Y = X ∩ (-∞, m)`, `Z = X ∩ [m, ∞)`, each a **proper** (non-empty, `≠ X`) subset. -/
theorem U_no_minimal {X : Set ℚ} (hX : U.mem X) :
    ∃ Y Z : Set ℚ, U.mem Y ∧ U.mem Z ∧ Y ∩ Z = ∅ ∧ Y ∪ Z = X ∧ Y ≠ X ∧ Z ≠ X := by
  obtain ⟨⟨L, rfl⟩, hne, hsub⟩ := hX
  obtain ⟨x, hx⟩ := hne
  obtain ⟨p, hp, hx1, hx2⟩ := mem_presentedIntervals.mp hx
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
    ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hlt⟩, hpm1⟩
  have hZne : (presentedIntervals L ∩ Set.Ici m).Nonempty :=
    ⟨m, mem_presentedIntervals.mpr ⟨p, hp, hpm1.le, hpm2⟩, le_refl m⟩
  refine ⟨_, _, ⟨⟨_, (presentedIntervals_map_clipLt m L).symm⟩, hYne,
      Set.inter_subset_left.trans hsub⟩,
    ⟨⟨_, (presentedIntervals_map_clipGe m L).symm⟩, hZne, Set.inter_subset_left.trans hsub⟩,
    hYZinter, hYZunion, ?_, ?_⟩
  · intro hEq
    have hZsub : presentedIntervals L ∩ Set.Ici m ⊆ presentedIntervals L ∩ Set.Iio m := by
      rw [hEq]; exact Set.inter_subset_left
    exact hZne.ne_empty ((Set.inter_eq_right.mpr hZsub).symm.trans hYZinter)
  · intro hEq
    have hYsub : presentedIntervals L ∩ Set.Iio m ⊆ presentedIntervals L ∩ Set.Ici m := by
      rw [hEq]; exact Set.inter_subset_left
    exact hYne.ne_empty ((Set.inter_eq_left.mpr hYsub).symm.trans hYZinter)

end DomainTheory.NeighbourhoodSystems
