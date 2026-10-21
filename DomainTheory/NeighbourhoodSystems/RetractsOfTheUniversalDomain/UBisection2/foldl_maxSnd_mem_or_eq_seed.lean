/-ai
The left fold of the maximum of second components from a seed equals the seed, or equals the second component of some pair in the list.

Induct on the list, generalizing the seed. The empty fold equals the seed. For a cons cell, compare the head's second component with the seed. If the head is at most the seed, the maximum is the seed and the inductive hypothesis yields the seed or a tail witness. If the seed is at most the head, the maximum is the head and the inductive hypothesis yields the head itself or a tail witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem foldl_maxSnd_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => max acc p.2) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => max acc q.2) seed = p.2 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total a.2 seed with hle | hle
    · rw [max_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [max_eq_right hle]
      rcases ih a.2 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩

end DomainTheory.NeighbourhoodSystems
