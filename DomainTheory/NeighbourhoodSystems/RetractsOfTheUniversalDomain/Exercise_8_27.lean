module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.piU

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem exercise_8_27 (d : ApproximableMap U U) : FinitaryProjection (piU d) :=
  isFinitaryProjection.piU d

end
