module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812e

@[expose] public section

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
