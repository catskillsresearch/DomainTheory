module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise822

@[expose] public section

open DomainTheory.NeighbourhoodSystems

/-- **Exercise 8.22 (Scott 1981, PRG-19).** `C ⊴ B` for Scott's examples. -/
theorem exercise_8_22 : Example44.C ⊴ ExampleB.B :=
  Exercise822.C_trianglelefteq_B

end
