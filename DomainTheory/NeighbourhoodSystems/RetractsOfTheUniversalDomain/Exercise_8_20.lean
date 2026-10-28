module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DiagonalRetracts

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

theorem exercise_8_20 {α : Type*} (D : NeighborhoodSystem α) :
    D ⊴ prod D D ∧ D ⊴ funSpace D D :=
  exercise_8_20_assembly D

end
