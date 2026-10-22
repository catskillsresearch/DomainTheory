module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.fin2_zero_subset_zero_one
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- **Example 8.4's `check` combinator.** `X check Y ↔ Y = {0,1} ∨ X ≠ Δ_D`. -/
def check : ApproximableMap D O where
  rel X Y := D.mem X ∧ O.mem Y ∧ (Y = ({0, 1} : Set (Fin 2)) ∨ X ≠ D.master)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨D.master_mem, O.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hY1⟩ ⟨-, hY', hY1'⟩
    refine ⟨hX, ?_, ?_⟩
    · rcases hY with rfl | rfl <;> rcases hY' with rfl | rfl
      · exact Or.inl (Set.inter_self _)
      · exact Or.inl (Set.inter_eq_left.mpr fin2_zero_subset_zero_one)
      · exact Or.inl (Set.inter_eq_right.mpr fin2_zero_subset_zero_one)
      · exact Or.inr (Set.inter_self _)
    · rcases hY1 with h1 | hXne
      · rcases hY1' with h1' | hXne'
        · left; rw [h1, h1']; simp
        · right; exact hXne'
      · right; exact hXne
  mono := by
    rintro X X' Y Y' ⟨hX, hY, hY1⟩ hXX' hYY' hX' hY'
    refine ⟨hX', hY', ?_⟩
    rcases hY1 with hYeq | hXne
    · left
      subst hYeq
      rcases hY' with rfl | rfl
      · exfalso
        have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
        have h2 : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := hYY' h1
        simp at h2
      · rfl
    · right
      intro hX'eq
      apply hXne
      exact Set.Subset.antisymm (D.sub_master hX) (hX'eq ▸ hXX')

end DomainTheory.NeighbourhoodSystems
