module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem

theorem foldl_maxSnd_seed_le (L : List (ℚ × ℚ)) (seed : ℚ) :
    seed ≤ L.foldl (fun acc p => max acc p.2) seed := by
  induction L generalizing seed with
  | nil => exact le_refl seed
  | cons a l ih =>
    rw [List.foldl_cons]
    exact (le_max_left seed a.2).trans (ih (max seed a.2))

end DomainTheory.NeighbourhoodSystems
