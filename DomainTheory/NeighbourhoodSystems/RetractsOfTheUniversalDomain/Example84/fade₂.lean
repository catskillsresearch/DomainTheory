/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.O_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.mem_Otop
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Example84.check_rel

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ApproximableMap₂

variable {α : Type*} {D : NeighborhoodSystem α}

/-- **Example 8.4's `fade` combinator, as a two-variable map.** `X, Y fade Z ↔ Z = Δ_D ∨ (X = {0}
∧ Y ⊆ Z)`: the master is always a safe output; `X = {0}` (the informative `O`-input) lets `Y` pass
straight through. -/
def fade₂ : ApproximableMap₂ O D D where
  rel X Y Z := O.mem X ∧ D.mem Y ∧ D.mem Z ∧ (Z = D.master ∨ (X = ({0} : Set (Fin 2)) ∧ Y ⊆ Z))
  rel_dom₀ h := h.1
  rel_dom₁ h := h.2.1
  rel_cod h := h.2.2.1
  master_rel := ⟨O.master_mem, D.master_mem, D.master_mem, Or.inl rfl⟩
  inter_right := by
    rintro X Y Z Z' ⟨hX, hY, hZ, hZ1⟩ ⟨-, -, hZ', hZ1'⟩
    refine ⟨hX, hY, ?_, ?_⟩
    · rcases hZ1 with rfl | ⟨-, hYZ⟩
      · rwa [Set.inter_eq_right.mpr (D.sub_master hZ')]
      · rcases hZ1' with rfl | ⟨-, hYZ'⟩
        · rwa [Set.inter_eq_left.mpr (D.sub_master hZ)]
        · exact D.inter_mem hZ hZ' hY (Set.subset_inter hYZ hYZ')
    · rcases hZ1 with rfl | ⟨hXeq, hYZ⟩
      · rcases hZ1' with rfl | ⟨hXeq', hYZ'⟩
        · left; exact Set.inter_self _
        · right
          refine ⟨hXeq', ?_⟩
          rw [Set.inter_eq_right.mpr (D.sub_master hZ')]
          exact hYZ'
      · right
        refine ⟨hXeq, ?_⟩
        rcases hZ1' with rfl | ⟨-, hYZ'⟩
        · rw [Set.inter_eq_left.mpr (D.sub_master hZ)]
          exact hYZ
        · exact Set.subset_inter hYZ hYZ'
  mono := by
    rintro X X' Y Y' Z Z' ⟨hX, hY, hZ, hZ1⟩ hXX' hYY' hZZ' hX' hY' hZ'
    refine ⟨hX', hY', hZ', ?_⟩
    rcases hZ1 with rfl | ⟨hXeq, hYZ⟩
    · left; exact Set.Subset.antisymm (D.sub_master hZ') hZZ'
    · have hX'eq : X' = ({0} : Set (Fin 2)) := by
        rcases hX' with rfl | rfl
        · rfl
        · exfalso
          have h1 : (1 : Fin 2) ∈ ({0, 1} : Set (Fin 2)) := by simp
          have h2 : (1 : Fin 2) ∈ X := hXX' h1
          rw [hXeq] at h2
          simp at h2
      right
      exact ⟨hX'eq, hYY'.trans (hYZ.trans hZZ')⟩

end DomainTheory.NeighbourhoodSystems
