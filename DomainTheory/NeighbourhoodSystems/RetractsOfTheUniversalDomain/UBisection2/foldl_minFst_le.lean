/-ai
The left fold of the minimum of first components from a seed is at most the first component of any pair in the list.

Induct on the list, generalizing the seed. The empty list has no members. For a cons cell, rewrite the fold. If the pair is the head, the remaining fold is at most the minimum of the seed and the first component by the seed inequality, and that minimum is at most the first component. If the pair lies in the tail, the inductive hypothesis at the updated seed applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_minFst_le_seed

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem foldl_minFst_le (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    L.foldl (fun acc q => min acc q.1) seed ≤ p.1 := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (foldl_minFst_le_seed l (min seed p.1)).trans (min_le_right seed p.1)
    · exact ih (min seed a.1) hp'

end DomainTheory.NeighbourhoodSystems
