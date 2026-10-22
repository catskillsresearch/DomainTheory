module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

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
