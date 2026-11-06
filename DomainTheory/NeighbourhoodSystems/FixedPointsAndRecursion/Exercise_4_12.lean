module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.idMap

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example_1_2_elements

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems.Exercise412
open NeighborhoodSystem ApproximableMap Example12 Example12.neighborhoodSystem

section

abbrev T : NeighborhoodSystem Example12.Token := Example12.neighborhoodSystem

theorem one_ne_zero : (Example12.one) ≠ Example12.zero := by
  intro h
  rw [Example12.one, Example12.zero, Set.ext_iff] at h
  have h1 : (1 : Example12.Token) = 0 := (h 1).mp rfl
  exact absurd h1 (by decide)

theorem one_ne_master : (Example12.one) ≠ Example12.master := by
  intro h
  rw [Example12.one, Example12.master, Set.ext_iff] at h
  have h0 : (0 : Example12.Token) ∈ ({1} : Set Example12.Token) := (h 0).mpr (Set.mem_univ 0)
  simp only [Set.mem_singleton_iff] at h0
  exact absurd h0 (by decide)

theorem zero_ne_master : (Example12.zero) ≠ Example12.master := by
  intro h
  rw [Example12.zero, Example12.master, Set.ext_iff] at h
  have h1 : (1 : Example12.Token) ∈ ({0} : Set Example12.Token) := (h 1).mpr (Set.mem_univ 1)
  simp only [Set.mem_singleton_iff] at h1
  exact absurd h1 (by decide)
end

section

theorem elemOne_not_le_elemZero : ¬ elemOne ≤ elemZero := by
  intro h
  rcases h Example12.one (Or.inr rfl) with hm | hz
  · exact one_ne_master hm
  · exact one_ne_zero hz
end

section

theorem elemZero_not_le_elemOne : ¬ elemZero ≤ elemOne := by
  intro h
  rcases h Example12.zero (Or.inr rfl) with hm | ho
  · exact zero_ne_master hm
  · exact one_ne_zero ho.symm
end

section

theorem idMap_fixed (x : T.Element) : (idMap T).toElementMap x = x := toElementMap_idMap x
end

section

theorem no_greatest_fixedPoint :
    ¬ ∃ z : T.Element, (idMap T).toElementMap z = z ∧
      ∀ x, (idMap T).toElementMap x = x → x ≤ z := by
  rintro ⟨z, _, hz⟩
  have h0 : elemZero ≤ z := hz elemZero (idMap_fixed elemZero)
  have h1 : elemOne ≤ z := hz elemOne (idMap_fixed elemOne)
  rcases element_classification z with rfl | rfl | rfl
  · exact (bot_lt_elemZero).2 h0
  · exact elemOne_not_le_elemZero h1
  · exact elemZero_not_le_elemOne h0
end

section

theorem example_412 :
    (∀ (x : T.Element), (idMap T).toElementMap x = x) ∧
    (¬ ∃ z : T.Element, (idMap T).toElementMap z = z ∧
        ∀ x, (idMap T).toElementMap x = x → x ≤ z) :=
  ⟨@idMap_fixed, @no_greatest_fixedPoint⟩
end

end DomainTheory.NeighbourhoodSystems.Exercise412
end
