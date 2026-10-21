/-ai
The left fold of the minimum of first components from a seed equals the seed, or equals the first component of some pair in the list.

Induct on the list, generalizing the seed. The empty fold equals the seed. For a cons cell, compare the seed with the head's first component. If the seed is at most the head, the minimum is the seed and the inductive hypothesis yields the seed or a tail witness. If the head is at most the seed, the minimum is the head and the inductive hypothesis yields the head itself or a tail witness.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem foldl_minFst_mem_or_eq_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed = seed ∨
      ∃ p ∈ L, L.foldl (fun acc q => min acc q.1) seed = p.1 := by
  induction L generalizing seed with
  | nil => exact Or.inl rfl
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases le_total seed a.1 with hle | hle
    · rw [min_eq_left hle]
      rcases ih seed with h | ⟨p, hp, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩
    · rw [min_eq_right hle]
      rcases ih a.1 with h | ⟨p, hp, h⟩
      · exact Or.inr ⟨a, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨p, List.mem_cons_of_mem a hp, h⟩

end DomainTheory.NeighbourhoodSystems
