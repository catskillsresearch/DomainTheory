module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise827

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

/-- **Exercise 8.27 (Scott 1981, PRG-19).** For a polymorphic type `d`, `Π(d)` is a type
(finitary projection). -/
theorem exercise_8_27 (d : ApproximableMap U U) : FinitaryProjection (piU d) :=
  isFinitaryProjection.piU d

end
