/-ai
The second component of any pair in a list of rational pairs is at most the left fold of the maximum of second components from any seed.

Induct on the list, generalizing the seed. The empty list has no members. For a cons cell, rewrite the fold. If the pair is the head, its second component is at most the maximum with the seed, and that maximum is at most the remaining fold by the seed inequality. If the pair lies in the tail, the inductive hypothesis at the updated seed applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UBisection2.foldl_maxSnd_seed_le

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem foldl_maxSnd_ge (L : List (ℚ × ℚ)) (seed : ℚ) (p : ℚ × ℚ) (hp : p ∈ L) :
    p.2 ≤ L.foldl (fun acc q => max acc q.2) seed := by
  induction L generalizing seed with
  | nil => cases hp
  | cons a l ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact (le_max_right seed p.2).trans (foldl_maxSnd_seed_le l (max seed p.2))
    · exact ih (max seed a.2) hp'

end DomainTheory.NeighbourhoodSystems
