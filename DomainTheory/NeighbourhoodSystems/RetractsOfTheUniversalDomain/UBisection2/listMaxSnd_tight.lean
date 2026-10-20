module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.listMaxSnd_attained

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

/-- **`listMaxSnd L` is arbitrarily approached from below by `presentedIntervals L`.** -/
theorem listMaxSnd_tight {L : List (ℚ × ℚ)} (hne : L ≠ [])
    (hpos : ∀ p ∈ L, p.1 < p.2) (hb : ∀ p ∈ L, 0 ≤ p.1 ∧ p.2 ≤ 1) {y : ℚ}
    (hy : y < listMaxSnd L) : ∃ x ∈ presentedIntervals L, y < x := by
  have hlb : ∀ p ∈ L, 0 < p.2 := fun p hp => lt_of_le_of_lt (hb p hp).1 (hpos p hp)
  obtain ⟨p, hp, hpeq⟩ := listMaxSnd_attained hne hlb
  rw [← hpeq] at hy
  rcases lt_or_ge y p.1 with hlt | hge
  · exact ⟨p.1, mem_presentedIntervals.mpr ⟨p, hp, le_refl _, hpos p hp⟩, hlt⟩
  · exact ⟨(y + p.2) / 2, mem_presentedIntervals.mpr ⟨p, hp, hge.trans (left_lt_add_div_two.mpr hy).le,
      add_div_two_lt_right.mpr hy⟩, left_lt_add_div_two.mpr hy⟩

end DomainTheory.NeighbourhoodSystems
