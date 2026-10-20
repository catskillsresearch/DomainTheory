/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619

/-- **The two-point generator `{{0},{0,Λ}}`.** Its tokens are `Δ = {0,Λ}`, with the one proper
neighbourhood `{0}` sitting strictly below the master `{0,Λ} = Δ`. As a domain this is the chain
`{0} ⊏ Δ` (one point above the bottom). Here `0 = [false]` and `Λ = []`. -/
def Cnat : ScottSys where
  sys :=
    { mem := fun X => X = {([false] : Str)} ∨ X = {([false] : Str), ([] : Str)}
      master := {([false] : Str), ([] : Str)}
      master_nonempty := ⟨[false], Set.mem_insert _ _⟩
      master_mem := Or.inr rfl
      inter_mem := by
        have hAB : ({([false] : Str)} : Set Str) ⊆ {([false] : Str), ([] : Str)} :=
          Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
        rintro X Y Z (rfl | rfl) (rfl | rfl) _ _
        · exact Or.inl (Set.inter_self _)
        · exact Or.inl (Set.inter_eq_self_of_subset_left hAB)
        · exact Or.inl (Set.inter_eq_self_of_subset_right hAB)
        · exact Or.inr (Set.inter_self _)
      sub_master := by
        have hAB : ({([false] : Str)} : Set Str) ⊆ {([false] : Str), ([] : Str)} :=
          Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
        rintro X (rfl | rfl)
        · exact hAB
        · exact subset_rfl }
  ne := by
    rintro X (rfl | rfl)
    · exact ⟨[false], rfl⟩
    · exact ⟨[false], Set.mem_insert _ _⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
