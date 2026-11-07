module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.ASharp_more

@[expose] public section

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

theorem example_821 {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    FinitaryProjection (aSharp a) :=
  isFinitaryProjection_aSharp ha

