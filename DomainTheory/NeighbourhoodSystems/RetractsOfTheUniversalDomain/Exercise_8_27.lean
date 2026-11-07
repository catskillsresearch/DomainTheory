module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.piU

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem example_827 (d : ApproximableMap U U) : FinitaryProjection (piU d) :=
  isFinitaryProjection.piU d

