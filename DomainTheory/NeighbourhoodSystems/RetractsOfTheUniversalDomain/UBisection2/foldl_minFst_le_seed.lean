/-ai
The left fold of the minimum of first components is at most its seed.

Induct on the list, generalizing the seed. The empty fold is the seed. For a cons cell, the remaining fold is at most the minimum of the seed and the head's first component by the inductive hypothesis, and that minimum is at most the seed.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem foldl_minFst_le_seed (L : List (ℚ × ℚ)) (seed : ℚ) :
    L.foldl (fun acc p => min acc p.1) seed ≤ seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (ih (min seed a.1)).trans (min_le_left seed a.1)

end DomainTheory.NeighbourhoodSystems
