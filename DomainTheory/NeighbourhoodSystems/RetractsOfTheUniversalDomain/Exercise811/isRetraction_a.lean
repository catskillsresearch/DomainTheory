/-ai
The approximable map a is a retraction: composing it with itself yields a.

Compare related pairs by extensionality of approximable maps. An intermediate interval forces the two middle endpoints to agree. Two strict steps compose, a strict step followed by the diagonal endpoint stays strict, a diagonal step followed by a strict step would force the right endpoint to be strictly less than itself, and two diagonal steps give the diagonal. Conversely, a strict relation is split by a rational strictly between the endpoints, giving two strict steps, and the diagonal case at 1 is the diagonal step through [0, 1) taken twice.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap


/-- **Exercise 8.11 (second part, retraction).** `a ∘ a = a`. -/
theorem isRetraction_a : IsRetraction a := by
  apply ApproximableMap.ext
  intro X Z
  constructor
  · rintro ⟨Y, ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, hcond1⟩,
      ⟨s', t, hs0', hs1', ht0, ht1, hYs', rfl, hcond2⟩⟩
    have hss' : s = s' := Ico0_inj hs0 hs0' hYs'
    subst hss'
    refine ⟨r, t, hr0, hr1, ht0, ht1, rfl, rfl, ?_⟩
    rcases hcond1 with h1 | ⟨rfl, rfl⟩
    · rcases hcond2 with h2 | ⟨rfl, rfl⟩
      · exact Or.inl (h1.trans h2)
      · exact Or.inl h1
    · rcases hcond2 with h2 | ⟨-, rfl⟩
      · exact absurd (h2.trans_le ht1) (lt_irrefl _)
      · exact Or.inr ⟨rfl, rfl⟩
  · rintro ⟨r, t, hr0, hr1, ht0, ht1, rfl, rfl, hcond⟩
    rcases hcond with h | ⟨rfl, rfl⟩
    · obtain ⟨s, hrs, hst⟩ := exists_between h
      have hs0 : 0 < s := hr0.trans hrs
      have hs1 : s ≤ 1 := (hst.trans_le ht1).le
      exact ⟨Set.Ico 0 s, ⟨r, s, hr0, hr1, hs0, hs1, rfl, rfl, Or.inl hrs⟩,
        ⟨s, t, hs0, hs1, ht0, ht1, rfl, rfl, Or.inl hst⟩⟩
    · exact ⟨Set.Ico 0 1, ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩,
        ⟨1, 1, one_pos, le_rfl, one_pos, le_rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩⟩⟩

end DomainTheory.NeighbourhoodSystems.Exercise811
