module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.TwoTokenElements

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem ApproximableMap TwoToken TwoToken.neighborhoodSystem

abbrev noGreatestFixedDomain : NeighborhoodSystem TwoToken.Token := TwoToken.neighborhoodSystem

theorem one_ne_zero : (TwoToken.one) ≠ TwoToken.zero := by
  intro h
  rw [TwoToken.one, TwoToken.zero, Set.ext_iff] at h
  have h1 : (1 : TwoToken.Token) = 0 := (h 1).mp rfl
  exact absurd h1 (by decide)

theorem one_ne_master : (TwoToken.one) ≠ TwoToken.master := by
  intro h
  rw [TwoToken.one, TwoToken.master, Set.ext_iff] at h
  have h0 : (0 : TwoToken.Token) ∈ ({1} : Set TwoToken.Token) := (h 0).mpr (Set.mem_univ 0)
  simp only [Set.mem_singleton_iff] at h0
  exact absurd h0 (by decide)

theorem zero_ne_master : (TwoToken.zero) ≠ TwoToken.master := by
  intro h
  rw [TwoToken.zero, TwoToken.master, Set.ext_iff] at h
  have h1 : (1 : TwoToken.Token) ∈ ({0} : Set TwoToken.Token) := (h 1).mpr (Set.mem_univ 1)
  simp only [Set.mem_singleton_iff] at h1
  exact absurd h1 (by decide)

theorem elemOne_not_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h TwoToken.one (Or.inr rfl) with hm | hz
  · exact one_ne_master hm
  · exact one_ne_zero hz

theorem elemZero_not_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h TwoToken.zero (Or.inr rfl) with hm | ho
  · exact zero_ne_master hm
  · exact one_ne_zero ho.symm

theorem idMap_fixed (x : noGreatestFixedDomain.Element) :
    (idMap noGreatestFixedDomain).toElementMap x = x := toElementMap_idMap x

theorem no_greatest_fixedPoint :
    ¬ ∃ z : noGreatestFixedDomain.Element, (idMap noGreatestFixedDomain).toElementMap z = z ∧
      ∀ x, (idMap noGreatestFixedDomain).toElementMap x = x → x ≤ z := by
  rintro ⟨z, _, hz⟩
  have h0 : elemZero ≤ z := hz elemZero (idMap_fixed elemZero)
  have h1 : elemOne ≤ z := hz elemOne (idMap_fixed elemOne)
  rcases element_classification z with rfl | rfl | rfl
  · exact (bot_lt_elemZero).2 h0
  · exact elemOne_not_le_elemZero h1
  · exact elemZero_not_le_elemOne h0

end DomainTheory.NeighbourhoodSystems
