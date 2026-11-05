module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ElementOrder
public import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Set.Card

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
namespace NeighborhoodSystem
section

variable {α : Type*} (V : NeighborhoodSystem α)

theorem eq_principal_of_isMin (x : V.Element) {X : Set α} (hX : x.mem X)
    (hmin : ∀ Y, x.mem Y → X ⊆ Y) : x = V.principal (x.sub hX) := by
  apply Element.ext
  intro Z
  constructor
  · intro hZ
    exact ⟨x.sub hZ, hmin Z hZ⟩
  · rintro ⟨hZmem, hXZ⟩
    exact x.up_mem hX hZmem hXZ

theorem exists_minimum_of_fintype [Fintype α] (x : V.Element) :
    ∃ X, x.mem X ∧ ∀ Y, x.mem Y → X ⊆ Y := by
  classical
  suffices aux : ∀ n (A : Set α), A.ncard = n → x.mem A →
      ∃ X, x.mem X ∧ X ⊆ A ∧ ∀ Y, x.mem Y → Y ⊆ A → X ⊆ Y from by
    obtain ⟨X, hX, _, hmin⟩ := aux V.master.ncard V.master rfl x.master_mem
    exact ⟨X, hX, fun Y hY => hmin Y hY (V.sub_master (x.sub hY))⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hn hA
    by_cases hleast : ∀ Y, x.mem Y → Y ⊆ A → A ⊆ Y
    · exact ⟨A, hA, subset_rfl, hleast⟩
    · push Not at hleast
      obtain ⟨Y, hY, hYA, hAY⟩ := hleast
      have hss : Y ⊂ A := ⟨hYA, hAY⟩
      have hlt : Y.ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard hss
      obtain ⟨X, hX, hXsub, hmin⟩ := ih Y.ncard hlt Y rfl hY
      refine ⟨X, hX, hXsub.trans hYA, ?_⟩
      intro Z hZ hZA
      have hcap : x.mem (Z ∩ Y) := x.inter_mem hZ hY
      exact (hmin (Z ∩ Y) hcap Set.inter_subset_right).trans Set.inter_subset_left

theorem element_eq_principal_of_fintype [Fintype α] (x : V.Element) :
    ∃ X, ∃ hX : V.mem X, x = V.principal hX := by
  obtain ⟨X, hX, hmin⟩ := V.exists_minimum_of_fintype x
  exact ⟨X, x.sub hX, V.eq_principal_of_isMin x hX hmin⟩

end

end NeighborhoodSystem
end DomainTheory.NeighbourhoodSystems
end
