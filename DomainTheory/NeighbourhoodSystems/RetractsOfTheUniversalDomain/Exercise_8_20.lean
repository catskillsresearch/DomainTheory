module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise820

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- **Exercise 8.20 (Scott 1981, PRG-19).** For any domain `D`, `D ⊴ D×D` and `D ⊴ D→D`. -/
theorem exercise_8_20 {α : Type*} (D : NeighborhoodSystem α) :
    D ⊴ prod D D ∧ D ⊴ funSpace D D :=
  exercise_8_20_assembly D

end
