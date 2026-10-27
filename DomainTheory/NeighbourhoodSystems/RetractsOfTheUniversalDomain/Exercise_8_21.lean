module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise821

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 8.21 (Scott 1981, PRG-19).** The sharp construction yields a finitary projection. -/
theorem exercise_8_21 {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    FinitaryProjection (aSharp a) :=
  isFinitaryProjection_aSharp ha

end
